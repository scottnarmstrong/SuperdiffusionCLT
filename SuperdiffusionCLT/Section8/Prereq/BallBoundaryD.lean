/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallBoundaryC
public import SuperdiffusionCLT.Section8.Prereq.BallExitTimeC
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAt

/-!
# Boundary continuity of the exit-time solution on Euclidean balls

For the coefficient `a = ν Id + k` with `k` a `C¹` skew field, the zero-trace solution `u` of
`lam u - ∇·(a∇u) = 1` on a Euclidean ball has a representative which is continuous on the whole
space and vanishes off the ball (`ballBdry_data`).

At a point `p` of the sphere the barrier is `ψ(x) = M (c - exp (-μ |x - e|²))` with `e = 2p - x₀`
the centre of the exterior ball of the same radius touching the sphere at `p`.  For `μ` large
(depending on `ν`, `r` and the divergence of `k` on the closed ball) `-∇·(a∇ψ) ≥ 1` in the ball and
`ψ ≥ 0` there, so `0 ≤ u ≤ ψ` (`ballBdry_upper`, from the comparison of `BallBoundaryC`), and `ψ(p) = 0`.
Together with the interior continuity of the part resolvent this gives continuity at every
boundary point (`ballBdry_continuous_of_barriers`).

The boundary hypothesis of the almost-sure ball theorem `ballExit_ae_ball` is thereby discharged
(`ballBdry_ae_data`), giving `ballBdry_ae_ball`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Topology
open SuperdiffusionCLT.Section8.DivergenceForm

variable {d : ℕ}

/-- A function that is continuous on an open set, zero off it, nonnegative on it, and dominated
by a continuous function vanishing at each boundary point, is continuous. -/
theorem ballBdry_continuous_of_barriers {V : Set (Vec d)} (hV : IsOpen V) {w : Vec d → ℝ}
    (hcont : ContinuousOn w V) (hoff : ∀ x, x ∉ V → w x = 0) (hnn : ∀ x ∈ V, 0 ≤ w x)
    (hbar : ∀ p ∈ frontier V, ∃ ψ : Vec d → ℝ, Continuous ψ ∧ ψ p = 0 ∧ ∀ x ∈ V, w x ≤ ψ x) :
    Continuous w := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hpV : p ∈ V
  · exact hcont.continuousAt (hV.mem_nhds hpV)
  by_cases hcl : p ∈ closure V
  · have hfr : p ∈ frontier V := by
      rw [frontier, hV.interior_eq]
      exact ⟨hcl, hpV⟩
    obtain ⟨ψ, hψc, hψp, hψ⟩ := hbar p hfr
    have hw0 : ∀ x, 0 ≤ w x := fun x => by
      by_cases hx : x ∈ V
      · exact hnn x hx
      · rw [hoff x hx]
    have hwle : ∀ x, w x ≤ max (ψ x) 0 := fun x => by
      by_cases hx : x ∈ V
      · exact (hψ x hx).trans (le_max_left _ _)
      · rw [hoff x hx]; exact le_max_right _ _
    have hg : Filter.Tendsto (fun x => max (ψ x) 0) (𝓝 p) (𝓝 0) := by
      have hgc : Continuous (fun x => max (ψ x) (0 : ℝ)) := hψc.max continuous_const
      have := hgc.tendsto p
      simpa [hψp] using this
    have := squeeze_zero hw0 hwle hg
    rw [ContinuousAt, hoff p hpV]
    exact this
  · have hmem : (closure V)ᶜ ∈ 𝓝 p := isClosed_closure.isOpen_compl.mem_nhds hcl
    have hev : w =ᶠ[𝓝 p] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset hmem fun x hx => hoff x (fun hxV => hx (subset_closure hxV))
    exact (continuousAt_const).congr hev.symm

theorem ballBdry_sq_eq_euclideanSqDist (e x : Vec d) :
    ballBdry_sq e x = euclideanSqDist x e := by
  unfold ballBdry_sq euclideanSqDist vecNormSq vecDot
  exact Finset.sum_congr rfl fun j _ => by simp [sq]

theorem ballBdry_frontier_ball {x₀ : Vec d} {r : ℝ} {p : Vec d}
    (hp : p ∈ frontier (euclideanBall x₀ r)) : euclideanSqDist p x₀ = r ^ 2 := by
  have hopen := isOpen_euclideanBall x₀ r
  rw [frontier, hopen.interior_eq] at hp
  obtain ⟨hcl, hnot⟩ := hp
  have hclosed : IsClosed {x : Vec d | euclideanSqDist x x₀ ≤ r ^ 2} :=
    isClosed_le (continuous_euclideanSqDist_left x₀) continuous_const
  have hsub : closure (euclideanBall x₀ r) ⊆ {x : Vec d | euclideanSqDist x x₀ ≤ r ^ 2} :=
    closure_minimal (fun x (hx : euclideanSqDist x x₀ < r ^ 2) => (le_of_lt hx : euclideanSqDist x x₀ ≤ r ^ 2)) hclosed
  have hle : euclideanSqDist p x₀ ≤ r ^ 2 := hsub hcl
  have hge : r ^ 2 ≤ euclideanSqDist p x₀ := by
    by_contra h
    exact hnot (lt_of_not_ge h)
  exact le_antisymm hle hge

theorem ballBdry_euclideanSqDist_eq (x y : Vec d) :
    euclideanSqDist x y = ∑ j, (x j - y j) ^ 2 := by
  unfold euclideanSqDist vecNormSq vecDot
  exact Finset.sum_congr rfl fun j _ => by simp [sq]

/-- Distances to the centre of the exterior ball of the same radius touching the sphere at `p`. -/
theorem ballBdry_dist_bounds {x₀ p x : Vec d} {r : ℝ} (hp : euclideanSqDist p x₀ = r ^ 2)
    (hx : euclideanSqDist x x₀ < r ^ 2) :
    r ^ 2 ≤ ballBdry_sq (fun j => 2 * p j - x₀ j) x ∧
      ballBdry_sq (fun j => 2 * p j - x₀ j) x ≤ (4 * r) ^ 2 := by
  rw [ballBdry_euclideanSqDist_eq] at hp hx
  have hlow : ∀ j, -(x j - x₀ j) ^ 2 + 2 * (p j - x₀ j) ^ 2 ≤ (x j - (2 * p j - x₀ j)) ^ 2 :=
    fun j => by nlinarith only [sq_nonneg ((x j - x₀ j) - (p j - x₀ j))]
  have hupp : ∀ j, (x j - (2 * p j - x₀ j)) ^ 2 ≤ 2 * (x j - x₀ j) ^ 2 + 8 * (p j - x₀ j) ^ 2 :=
    fun j => by nlinarith only [sq_nonneg ((x j - x₀ j) + 2 * (p j - x₀ j))]
  have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlow j)
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hupp j)
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hp] at h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp] at h2
  unfold ballBdry_sq
  constructor
  · linarith only [h1, hx]
  · nlinarith only [h2, hx, sq_nonneg r]

theorem ballBdry_continuous_colDiv {k : Vec d → Mat d} (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j))
    (j : Fin d) : Continuous (fun x => ballBdry_colDiv k x j) := by
  unfold ballBdry_colDiv
  refine continuous_finsetSum _ fun i _ => ?_
  simpa using ((hk i j).continuous_fderiv (by simp)).clm_apply continuous_const

/-- **The upper barrier at a point of the sphere.**  A zero-trace solution of `lam u - ∇·(a∇u) = 1`
on a ball is dominated by a continuous function vanishing at any prescribed boundary point. -/
theorem ballBdry_upper {ν : ℝ} (hν : 0 < ν) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (hskew : ∀ x i j, k x i j = -k x j i)
    {lam : ℝ} (hlam : 0 < lam) {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    (u : H10Function (euclideanBall x₀ r))
    (hu : IsScalarForcedWeakSolution (fun x => ν • (1 : Mat d) + k x) (euclideanBall x₀ r)
      (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function)
    {p : Vec d} (hp : euclideanSqDist p x₀ = r ^ 2) :
    ∃ ψ : Vec d → ℝ, Continuous ψ ∧ ψ p = 0 ∧
      ∀ᵐ x ∂(volumeMeasureOn (euclideanBall x₀ r)), u.toH1Function.toFun x ≤ ψ x := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr
  have hcompact : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hUR : euclideanBall x₀ r ⊆ Metric.closedBall x₀ r :=
    (euclideanBall_subset_metricBall hr).trans Metric.ball_subset_closedBall
  have hcont : Continuous (fun x => ∑ j, |ballBdry_colDiv k x j|) :=
    continuous_finsetSum _ fun j _ => continuous_abs.comp (ballBdry_continuous_colDiv hk j)
  obtain ⟨Kb, hKb⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  set Y : ℝ := 4 * r with hY
  have hY0 : 0 ≤ Y := by positivity
  set μ : ℝ := (ν * d + |Kb| * Y + 1) / (2 * ν * r ^ 2) + 1 with hμ
  have hμ0 : 0 < μ := by positivity
  have hμbig : ν * (d : ℝ) + |Kb| * Y + 1 ≤ 2 * μ * ν * r ^ 2 := by
    have : 2 * μ * ν * r ^ 2 = (ν * d + |Kb| * Y + 1) + 2 * ν * r ^ 2 := by
      rw [hμ]; field_simp
    rw [this]
    have : 0 < 2 * ν * r ^ 2 := by positivity
    linarith only [this]
  set e : Vec d := fun j => 2 * p j - x₀ j with he
  set M : ℝ := Real.exp (μ * Y ^ 2) / (2 * μ) with hM
  set c : ℝ := Real.exp (-μ * r ^ 2) with hc
  have hsp : ballBdry_sq e p = r ^ 2 := by
    rw [ballBdry_sq_eq_euclideanSqDist, ballBdry_euclideanSqDist_eq, ← hp,
      ballBdry_euclideanSqDist_eq]
    exact Finset.sum_congr rfl fun j _ => by simp only [he]; ring
  refine ⟨ballBdry_psi M μ c e, (ballBdry_contDiff_psi M μ c e (n := 0)).continuous, ?_, ?_⟩
  · unfold ballBdry_psi ballBdry_gauss
    rw [hsp]
    simp [hc]
  · have hψ0 : ∀ x ∈ euclideanBall x₀ r, 0 ≤ ballBdry_psi M μ c e x := fun x hx => by
      have hb := (ballBdry_dist_bounds hp hx).1
      unfold ballBdry_psi
      have hM0 : 0 ≤ M := by positivity
      refine mul_nonneg hM0 (sub_nonneg.mpr ?_)
      unfold ballBdry_gauss
      exact Real.exp_le_exp.mpr (by nlinarith only [hb, hμ0])
    have hψfd : ∀ x, (fun j => fderiv ℝ (ballBdry_psi M μ c e) x (basisVec j)) =
        ballBdry_grad M μ e x := fun x => funext fun j => ballBdry_psi_apply_basis M μ c e x j
    have hfun : (fun x => matVecMul (ν • (1 : Mat d) + k x)
        (fun j => fderiv ℝ (ballBdry_psi M μ c e) x (basisVec j))) =
        ballBdry_flux ν k M μ e := funext fun x => by
      rw [hψfd x]; rfl
    refine ballBdry_compare hV hν hk hskew hlam u hu
      (ballBdry_contDiff_psi M μ c e (n := 1)) hψ0 hr.le hUR ?_ ?_
    · intro i
      have h := ballBdry_contDiff_flux ν hk M μ e i
      rw [← hfun] at h
      exact h
    · intro x hx
      rw [hfun]
      have hb := ballBdry_dist_bounds hp hx
      refine ballBdry_neg_div_flux_ge ν hk hskew hμ0 hν hY0 hμbig e x hb.1 hb.2 ?_
      have := hKb x (hUR hx)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))

theorem ballBdry_skew_entry {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (x : Vec d)
    (i j : Fin d) : k x i j = -k x j i := by
  have h := congrFun (congrFun (D.skew x) j) i
  simpa [matTranspose, Matrix.transpose_apply] using h

variable [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **Boundary continuity on Euclidean balls.**  For the field `ν Id + k` with `k` skew and `C¹`,
the zero-trace solution of `lam u - ∇·(a∇u) = 1` on a Euclidean ball has a representative
which is continuous on the whole space and vanishes off the ball. -/
theorem ballBdry_data (D : FieldInputData d nu k) (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r)
        (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr
  set A := D.analyticData with hA
  set mu : MarkovProcess.Semigroup.PositiveShift := ⟨lam, hlam⟩ with hmu
  have hf := ballExit_measurable_datum (d := d) (V := euclideanBall x₀ r) hV.isOpen
  have hfD := ballExit_abs_datum_le (d := d) (euclideanBall x₀ r)
  set w₀ := A.partC0Resolvent hV mu _ hf hfD with hw₀
  have hrep : w₀ =ᵐ[volumeMeasureOn (euclideanBall x₀ r)] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a (show (0 : ℝ) < ((mu : MarkovProcess.Semigroup.PositiveShift) : ℝ) from mu.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)) := by
    filter_upwards [A.partC0Resolvent_ae hV mu _ hf hfD] with y hy
    exact hy
  obtain ⟨u, hwu, hsol⟩ := ballExit_exists_h10_solution A hV mu hrep
  have hcontOn : ContinuousOn w₀ (euclideanBall x₀ r) := A.continuousOn_partC0Resolvent hV mu _ hf hfD
  have hoff : ∀ y, y ∉ euclideanBall x₀ r → w₀ y = 0 := fun y hy =>
    A.partC0Resolvent_of_notMem hV mu _ hf hfD hy
  have hnn : ∀ y ∈ euclideanBall x₀ r, 0 ≤ w₀ y := fun y _ =>
    A.partC0Resolvent_nonneg hV mu _ hf (ballExit_datum_nonneg _) hfD y
  refine ⟨w₀, u, ?_, hoff, hwu, hsol⟩
  refine ballBdry_continuous_of_barriers hV.isOpen hcontOn hoff hnn fun p hp => ?_
  obtain ⟨ψ, hψc, hψp, hψ⟩ := ballBdry_upper D.nu_pos (fun i j => D.contDiff_entry i j)
    (ballBdry_skew_entry D) hlam hr u hsol (ballBdry_frontier_ball hp)
  refine ⟨ψ, hψc, hψp, fun x hx => ?_⟩
  refine le_of_ae_le_of_continuousOn hV.isOpen hcontOn hψc.continuousOn ?_ x hx
  filter_upwards [hwu, hψ] with y h1 h2
  rw [h1]
  exact h2

open ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped ENNReal NNReal ZeroAtInfty Matrix.Norms.Elementwise
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup

/-- **The boundary hypothesis of the almost-sure ball theorem, discharged.**  Almost surely, for
every centre, radius and shift, the zero-trace solution on the ball has a continuous
representative vanishing off the ball. -/
theorem ballBdry_ae_data {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ (x₀ : Vec d) {r : ℝ}, 0 < r →
      ∀ lam : ℝ, 0 < lam →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
  obtain ⟨D⟩ := hD
  intro x₀ r hr lam hlam
  exact ballBdry_data D x₀ hr hlam

/-- **The exit-time identification on Euclidean balls, almost surely, with no extra hypothesis.**
Almost surely the process of the marginal field has, under every continuous-path law, the
Laplace transform of the exit time from every Euclidean ball equal to `1 - lam w`, with `w` the
continuous `H¹₀`-solution of `lam u - ∇·(a∇u) = 1`, together with the Chernoff bound for early
exit. -/
theorem ballBdry_ae_ball {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          R.kernelSemigroup.IsConservative ∧ R.kernelSemigroup.IsFellerKernelSemigroup ∧
          A.KernelResolventIdentifiesAnalyticMinimal R ∧
          (∃ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q) ∧
          ∀ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q → ∀ (x₀ : Vec d) {r : ℝ}, 0 < r →
              ∀ lam : ℝ, 0 < lam → ∀ x ∈ euclideanBall x₀ r,
              ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
                (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
                (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
                IsScalarForcedWeakSolution A.a (euclideanBall x₀ r)
                  (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function ∧
                ∫⁻ path, ({path | ContinuousPath.exitTime (euclideanBall x₀ r) path < ⊤} :
                      Set _).indicator
                    (fun path => ENNReal.ofReal (Real.exp (-lam *
                      (ContinuousPath.exitTime (euclideanBall x₀ r) path).toReal))) path
                    ∂(Q x) = ENNReal.ofReal (1 - lam * w x) ∧
                ∀ s : ℝ, 0 ≤ s →
                  Q x {path | ContinuousPath.exitTime (euclideanBall x₀ r) path ≤
                      ENNReal.ofReal s} ≤
                    ENNReal.ofReal (Real.exp (lam * s)) * ENNReal.ofReal (1 - lam * w x) :=
  ballExit_ae_ball hPrefix hJ3 hnu (ballBdry_ae_data hPrefix hJ3 hnu)

/-! ## Satisfiability witnesses -/

/-- The zero (heat) field carries the process input: `k = 0` is skew, `C¹`, with zero gradient. -/
def ballBdry_heatInput (hd : 2 ≤ d) (hnu : 0 < nu) : FieldInputData d nu (fun _ => (0 : Mat d)) where
  two_le := hd
  nu_pos := hnu
  skew := fun y => by simp [matTranspose]
  contDiff := contDiff_const
  gradConst := 0
  gradConst_nonneg := le_rfl
  grad_le := fun y => by simp

/-- Witness for `ballBdry_data`: the heat field on the unit ball. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall (0 : Vec d) 1)), Continuous w ∧
      (∀ y, y ∉ euclideanBall (0 : Vec d) 1 → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) 1), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution (ballBdry_heatInput (nu := nu) hd hnu).analyticData.a
        (euclideanBall (0 : Vec d) 1) (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function :=
  ballBdry_data (ballBdry_heatInput hd hnu) 0 one_pos hlam

/-- Witness for `ballBdry_ae_data`: the Dirac law on the zero shell sequence. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ (x₀ : Vec d) {r : ℝ}, 0 < r → ∀ lam : ℝ, 0 < lam →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function :=
  ballBdry_ae_data (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

/-- Witness for `ballBdry_ae_ball`: under the Dirac law the almost-sure statement is available. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧
          ∃ Q : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw R.kernelSemigroup Q := by
  filter_upwards [ballBdry_ae_ball
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu] with omega h
  obtain ⟨A, R, h1, -, -, -, -, h6, -⟩ := h
  exact ⟨A, R, h1, h6⟩

end SuperdiffusionCLT.Section8
