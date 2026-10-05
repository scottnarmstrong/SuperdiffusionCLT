/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallExitTimeB
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import SuperdiffusionCLT.Section8.Common.Regularity.Ported.HarmonicReplacement
public import SuperdiffusionCLT.Section8.DivergenceForm.Regularity.ScalarWeakMaximumPrinciple
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldGeneralDomain
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldInterchange
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldLower
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueHarmonicDensity
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationWhole
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.PartResolventAlgebra

/-!
# The elliptic exit identification on Euclidean balls, for the marginal field

For a bounded convex domain `V` (in particular a Euclidean ball) and a shift `lam > 0`, let `w` be
a continuous function on `ℝ^d` which vanishes off `V` and agrees in `V` with the zero-trace
`H¹₀(V)` weak solution `u` of `lam u - ∇·(a∇u) = 1`.  Then for every continuous-path law `Q` of the
process of `∇·(ν Id + k)∇`, at every `x ∈ V`,

`E^x[e^{-lam T_V}] = 1 - lam w x`,

so `1 - lam w` is the `H¹` solution of `lam v - ∇·(a∇v) = 0` in `V` with `v = 1` on `∂V`, and
`Q x {T_V ≤ s} ≤ e^{lam s} (1 - lam w x)`.

The continuity of `w` up to the boundary is the only boundary input.  On axis cubes it is proved
(`ballExit_axisCube_data`, almost surely in `ballExit_ae_axisCube`).  On a Euclidean ball it
is the boundary continuity of the Dirichlet solution, carried as an explicit almost-sure
hypothesis in `ballExit_ae_ball`.

* `ballExit_anchorSet_eq`: the set `{y | |ε y| < 1}` is the Euclidean ball of radius `ε⁻¹`;
* `ballExit_rep_of_weakSolution`: a weak solution is the part solution;
* `ballExit_laplace_convex`, `ballExit_exitTime_le_convex`: the identification and the Chernoff
  bound on a bounded convex domain;
* `ballExit_axisCube_data`: the unconditional boundary data on axis cubes;
* `ballExit_ae_convex`, `ballExit_ae_ball`, `ballExit_ae_axisCube`: the almost-sure forms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory ProbabilityTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

/-- The set of the exit-time estimate, `{y | |ε y| < 1}`, is the Euclidean ball of radius `ε⁻¹`. -/
theorem ballExit_anchorSet_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    {y : Vec d | vecNormSq (ε • y) < 1} = euclideanBall (0 : Vec d) ε⁻¹ := by
  ext y
  have h : vecNormSq (ε • y) = ε ^ 2 * vecNormSq y := vecNormSq_smul ε y
  have hy : euclideanSqDist y 0 = vecNormSq y := by simp [euclideanSqDist]
  simp only [Set.mem_ofPred_eq, euclideanBall, hy, h]
  have h2 : 0 < ε ^ 2 := by positivity
  rw [inv_pow, ← one_div, lt_div_iff₀ h2, mul_comm]

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)

/-- **A zero-trace weak solution of the shifted equation is the part solution.**  A function `w`
which agrees almost everywhere with an `H¹₀(V)` weak solution `u` of
`-∇·(a∇u) = 1 - lam u` represents the shifted zero-trace solution of the constant one. -/
theorem ballExit_rep_of_weakSolution (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {lam : ℝ} (hlam : 0 < lam) {w : Vec d → ℝ}
    {u : H10Function V} (hwu : ∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y)
    (hsol : IsScalarForcedWeakSolution A.a V (fun y => 1 - lam * u.toH1Function.toFun y)
      u.toH1Function) :
    w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a hlam A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)) := by
  have hG : ∀ᵐ y ∂volumeMeasureOn V,
      ballExit_datumL2 hV y = (1 - lam * u.toH1Function.toFun y) + lam * u.toH1Function.toFun y := by
    filter_upwards [ballExit_datumL2_ae hV] with y hy
    rw [hy]
    ring
  have hweak := isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution hV u hsol _ hG
  have heq := (isAlphaShiftedWeakSolution_iff_eq A.a hlam A.hnu (partEllipticity A hV) _ _).1 hweak
  have hval := congrArg ZeroTraceSobolev.toL2 heq
  rw [ZeroTraceSobolev.toL2_ofH10Function] at hval
  filter_upwards [hwu, u.toH1Function.coeFn_toScalarL2] with y h1 h2
  rw [h1, ← h2, hval]

/-- **Laplace transform of the exit time from a bounded convex domain, `H¹` form.**  Let `w` be a
continuous function which vanishes off `V` and agrees almost everywhere in `V` with a zero-trace
weak solution `u` of `lam u - ∇·(a∇u) = 1`.  Then for every continuous-path law of the process of
the marginal field, `E^x[e^{-lam T_V}] = 1 - lam w x` at every `x ∈ V`. -/
theorem ballExit_laplace_convex {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {lam : ℝ}
    (hlam : 0 < lam) {w : Vec d → ℝ} (u : H10Function V) (hw : Continuous w)
    (hoff : ∀ y, y ∉ V → w y = 0)
    (hwu : ∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y)
    (hsol : IsScalarForcedWeakSolution D.analyticData.a V
      (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ V) :
    ∫⁻ path, ({path | ContinuousPath.exitTime V path < ⊤} : Set _).indicator
        (fun path => ENNReal.ofReal (Real.exp (-lam *
          (ContinuousPath.exitTime V path).toReal))) path ∂(Q x) =
      ENNReal.ofReal (1 - lam * w x) :=
  ballExit_lintegral_exp_neg_exitTime D hV ⟨lam, hlam⟩ hw hoff
    (ballExit_rep_of_weakSolution D.analyticData hV hlam hwu hsol) hQ hx

/-- **Early exit from a bounded convex domain.**  `Q x {T_V ≤ s} ≤ e^{lam s} (1 - lam w x)`. -/
theorem ballExit_exitTime_le_convex {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {lam : ℝ}
    (hlam : 0 < lam) {w : Vec d → ℝ} (u : H10Function V) (hw : Continuous w)
    (hoff : ∀ y, y ∉ V → w y = 0)
    (hwu : ∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y)
    (hsol : IsScalarForcedWeakSolution D.analyticData.a V
      (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ V) {s : ℝ} (hs : 0 ≤ s) :
    Q x {path | ContinuousPath.exitTime V path ≤ ENNReal.ofReal s} ≤
      ENNReal.ofReal (Real.exp (lam * s)) * ENNReal.ofReal (1 - lam * w x) := by
  have h := ballExit_measure_exitTime_le_le D hV ⟨lam, hlam⟩ hw hoff
    (ballExit_rep_of_weakSolution D.analyticData hV hlam hwu hsol) hQ hx s.toNNReal
  have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  rw [hs'] at h
  exact h

/-- **The continuous part solution on an axis cube, in `H¹` form.**  On an axis cube the continuous
zero extension of the part solution comes from the boundary reflection of the regularity layer. -/
theorem ballExit_axisCube_data (z : Vec d) {L : ℝ} (hL : 0 < L) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (w : Vec d → ℝ) (u : H10Function (axisCube z L)), Continuous w ∧
      (∀ y, y ∉ axisCube z L → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (axisCube z L), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (axisCube z L)
        (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function := by
  have hV := isOpenBoundedConvexDomain_axisCube z L
  obtain ⟨w, hw, hoff, hrep⟩ := exists_continuous_partSolution_zeroExtension D.analyticData z hL
    (partEllipticity D.analyticData hV) ⟨lam, hlam⟩ (ballExit_measurable_datum hV.isOpen)
    (ballExit_abs_datum_le (axisCube z L))
  obtain ⟨u, hwu, hsol⟩ := ballExit_exists_h10_solution D.analyticData hV ⟨lam, hlam⟩ hrep
  exact ⟨w, u, hw, hoff, hwu, hsol⟩

/-- **The exit-time identification on a family of bounded convex domains, almost surely.**
Suppose that almost surely, for every domain `V` of the family and every shift `lam > 0`, there is
a continuous function vanishing off `V` and agreeing in `V` with a zero-trace weak solution of
`lam u - ∇·(a∇u) = 1`.  Then almost surely the process of the marginal field, under every
continuous-path law `Q`, has Laplace transform of the exit time from `V` equal to `1 - lam w`, at
every point of `V`, together with the Chernoff bound for early exit. -/
theorem ballExit_ae_convex {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu)
    (𝒱 : Set (Set (Vec d))) (h𝒱 : ∀ V ∈ 𝒱, IsOpenBoundedConvexDomain V)
    (hbdry : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ V ∈ 𝒱, ∀ lam : ℝ, 0 < lam →
      ∃ (w : Vec d → ℝ) (u : H10Function V), Continuous w ∧ (∀ y, y ∉ V → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) V
          (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          R.kernelSemigroup.IsConservative ∧ R.kernelSemigroup.IsFellerKernelSemigroup ∧
          A.KernelResolventIdentifiesAnalyticMinimal R ∧
          (∃ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q) ∧
          ∀ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q → ∀ V ∈ 𝒱, ∀ lam : ℝ, 0 < lam →
              ∀ x ∈ V, ∃ (w : Vec d → ℝ) (u : H10Function V), Continuous w ∧
                (∀ y, y ∉ V → w y = 0) ∧
                (∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y) ∧
                IsScalarForcedWeakSolution A.a V
                  (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function ∧
                ∫⁻ path, ({path | ContinuousPath.exitTime V path < ⊤} : Set _).indicator
                    (fun path => ENNReal.ofReal (Real.exp (-lam *
                      (ContinuousPath.exitTime V path).toReal))) path ∂(Q x) =
                  ENNReal.ofReal (1 - lam * w x) ∧
                ∀ s : ℝ, 0 ≤ s →
                  Q x {path | ContinuousPath.exitTime V path ≤ ENNReal.ofReal s} ≤
                    ENNReal.ofReal (Real.exp (lam * s)) * ENNReal.ofReal (1 - lam * w x) := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu, hbdry] with omega hD hb
  obtain ⟨D⟩ := hD
  refine ⟨D.analyticData, D.logGrowthBounds.resolvent, rfl, rfl,
    D.logGrowthBounds.isConservative_kernelSemigroup,
    D.logGrowthBounds.resolvent.isFellerKernelSemigroup_kernelSemigroup,
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal,
    procConstr_exists_isContinuousPathLaw D.logGrowthBounds.processInput
      D.logGrowthBounds.isConservative_kernelSemigroup, ?_⟩
  intro Q hQ V hV lam hlam x hx
  obtain ⟨w, u, hw, hoff, hwu, hsol⟩ := hb V hV lam hlam
  exact ⟨w, u, hw, hoff, hwu, hsol,
    ballExit_laplace_convex D (h𝒱 V hV) hlam u hw hoff hwu hsol hQ hx,
    fun s hs => ballExit_exitTime_le_convex D (h𝒱 V hV) hlam u hw hoff hwu hsol hQ hx hs⟩

/-- **The exit-time identification on Euclidean balls, almost surely.**  Under the almost-sure
boundary continuity of the Dirichlet solution on balls (the hypothesis `hbdry`), almost surely
the process of the marginal field has, under every continuous-path law, the Laplace transform of
the exit time from every Euclidean ball equal to `1 - lam w`, with `w` the continuous
`H¹₀`-solution of `lam u - ∇·(a∇u) = 1`, together with the Chernoff bound for early exit. -/
theorem ballExit_ae_ball {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu)
    (hbdry : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ (x₀ : Vec d) {r : ℝ}, 0 < r →
      ∀ lam : ℝ, 0 < lam →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function) :
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
                    ENNReal.ofReal (Real.exp (lam * s)) * ENNReal.ofReal (1 - lam * w x) := by
  filter_upwards [ballExit_ae_convex hPrefix hJ3 hnu
    {V | ∃ (x₀ : Vec d) (r : ℝ), 0 < r ∧ V = euclideanBall x₀ r}
    (by
      rintro V ⟨x₀, r, hr, rfl⟩
      exact SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
        x₀ hr)
    (by
      filter_upwards [hbdry] with omega hb
      rintro V ⟨x₀, r, hr, rfl⟩ lam hlam
      exact hb x₀ hr lam hlam)] with omega h
  obtain ⟨A, R, h1, h2, h3, h4, h5, h6, hall⟩ := h
  exact ⟨A, R, h1, h2, h3, h4, h5, h6, fun Q hQ x₀ r hr lam hlam x hx =>
    hall Q hQ _ ⟨x₀, r, hr, rfl⟩ lam hlam x hx⟩

/-- **The exit-time identification on axis cubes, almost surely, with no extra hypothesis.**
The cubes are arbitrary axis cubes `z + (0, L)^d` of `ℝ^d`. -/
theorem ballExit_ae_axisCube {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          R.kernelSemigroup.IsConservative ∧ R.kernelSemigroup.IsFellerKernelSemigroup ∧
          A.KernelResolventIdentifiesAnalyticMinimal R ∧
          (∃ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q) ∧
          ∀ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q → ∀ (z : Vec d) {L : ℝ}, 0 < L →
              ∀ lam : ℝ, 0 < lam → ∀ x ∈ axisCube z L,
              ∃ (w : Vec d → ℝ) (u : H10Function (axisCube z L)), Continuous w ∧
                (∀ y, y ∉ axisCube z L → w y = 0) ∧
                (∀ᵐ y ∂volumeMeasureOn (axisCube z L), w y = u.toH1Function.toFun y) ∧
                IsScalarForcedWeakSolution A.a (axisCube z L)
                  (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function ∧
                ∫⁻ path, ({path | ContinuousPath.exitTime (axisCube z L) path < ⊤} :
                      Set _).indicator
                    (fun path => ENNReal.ofReal (Real.exp (-lam *
                      (ContinuousPath.exitTime (axisCube z L) path).toReal))) path
                    ∂(Q x) = ENNReal.ofReal (1 - lam * w x) ∧
                ∀ s : ℝ, 0 ≤ s →
                  Q x {path | ContinuousPath.exitTime (axisCube z L) path ≤
                      ENNReal.ofReal s} ≤
                    ENNReal.ofReal (Real.exp (lam * s)) * ENNReal.ofReal (1 - lam * w x) := by
  filter_upwards [ballExit_ae_convex hPrefix hJ3 hnu
    {V | ∃ (z : Vec d) (L : ℝ), 0 < L ∧ V = axisCube z L}
    (by
      rintro V ⟨z, L, hL, rfl⟩
      exact isOpenBoundedConvexDomain_axisCube z L)
    (by
      filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
      obtain ⟨D⟩ := hD
      rintro V ⟨z, L, hL, rfl⟩ lam hlam
      exact ballExit_axisCube_data D z hL hlam)] with omega h
  obtain ⟨A, R, h1, h2, h3, h4, h5, h6, hall⟩ := h
  exact ⟨A, R, h1, h2, h3, h4, h5, h6, fun Q hQ z L hL lam hlam x hx =>
    hall Q hQ _ ⟨z, L, hL, rfl⟩ lam hlam x hx⟩

/-! ## Satisfiability witnesses -/

/-- The unconditional axis-cube statement holds for the law concentrated on the zero shell
sequence: the zero skew field, with the process and its continuous-path law. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧
          (∃ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q) ∧
          ∀ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw R.kernelSemigroup Q → ∀ (z : Vec d) {L : ℝ}, 0 < L →
              ∀ lam : ℝ, 0 < lam → ∀ x ∈ axisCube z L,
              ∃ (w : Vec d → ℝ) (u : H10Function (axisCube z L)), Continuous w ∧
                (∀ y, y ∉ axisCube z L → w y = 0) ∧
                IsScalarForcedWeakSolution A.a (axisCube z L)
                  (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function ∧
                ∫⁻ path, ({path | ContinuousPath.exitTime (axisCube z L) path < ⊤} :
                      Set _).indicator
                    (fun path => ENNReal.ofReal (Real.exp (-lam *
                      (ContinuousPath.exitTime (axisCube z L) path).toReal))) path
                    ∂(Q x) = ENNReal.ofReal (1 - lam * w x) := by
  filter_upwards [ballExit_ae_axisCube
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu] with omega h
  obtain ⟨A, R, h1, -, -, -, -, h6, hall⟩ := h
  exact ⟨A, R, h1, h6, fun Q hQ z L hL lam hlam x hx => by
    obtain ⟨w, u, hw, hoff, -, hsol, hlap, -⟩ := hall Q hQ z hL lam hlam x hx
    exact ⟨w, u, hw, hoff, hsol, hlap⟩⟩

end
end SuperdiffusionCLT.Section8
