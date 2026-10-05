module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed


/-!
# Theorem A — comparator challenge

A Mathlib-only statement of Theorem A of Armstrong–Bou-Rabee–Kuusi, *Superdiffusive central
limit theorem for a Brownian particle in a critically-correlated incompressible random drift*
(arXiv:2404.01115): the quenched superdiffusive invariance principle.

The random environment is a sequence `ω = (jₙ)ₙ` of shells: `C²` skew-symmetric matrix fields on
`ℝ^d`, `d ≥ 2`, with joint law `P` subject to the standing assumptions (prefix: stationarity) and
(J1)–(J5). The stream matrix is `k = ∑ₙ jₙ` and the diffusion has generator
`∇·(ν Id + k − k(0))∇`. For `P`-almost every `ω` the diffusion exists; for every such diffusion
and every starting point, the rescaled path `t ↦ |log ε²|^{-1/4} ε X_{t/ε²}` converges in law,
as `ε → 0⁺`, to `√(2 c⋆^{1/2}) W` with `W` a standard Brownian motion; and the mean squared
displacement grows like `2 d c⋆^{1/2} t (log t)^{1/2}`, with quenched and annealed error bounds.

Every object of the statement is defined below from Mathlib primitives. `DESIGN.md` lists the
library object each definition equals and every presentation choice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.StatementAudit.TheoremA

noncomputable section

/-! ## 1. Euclidean vocabulary -/

/-- Vectors of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices (elementwise norm). -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Matrix-valued coefficient fields on `ℝ^d`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

variable {d : ℕ}

/-- The Euclidean norm `|x|`. -/
def vecNorm (x : Vec d) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖

/-- The squared Euclidean norm `|x|² = ∑ᵢ xᵢ²`. -/
def vecNormSq (x : Vec d) : ℝ := ∑ i, x i * x i

/-- The Euclidean operator norm of a matrix. -/
def matrixOperatorNorm (A : Mat d) : ℝ := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- Signed permutation matrices `R e_j = s_j e_{σ j}`, `s_j = ±1` (the hyperoctahedral group). -/
def IsSignedPermutationMatrix (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ i j, R i j = if i = σ j then s j else 0

/-! ## 2. Shells -/

/-- A shell: a `C²` skew-symmetric matrix field `j`, stored together with its first and second
derivatives as continuous maps, with exact derivative compatibility. -/
def ShellField (d : ℕ) :=
  { p : C(Vec d, Mat d) × (C(Vec d, Vec d →L[ℝ] Mat d) ×
      C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧ (∀ x, HasFDerivAt p.2.1 (p.2.2 x) x) ∧
      ∀ x i j, p.1 x i j = -p.1 x j i }

/-- The product of the compact-open topologies on the value and the two derivatives. -/
instance (d : ℕ) : TopologicalSpace (ShellField d) := by
  unfold ShellField
  infer_instance

/-- Shells carry the Borel σ-algebra. -/
instance (d : ℕ) : MeasurableSpace (ShellField d) := borel (ShellField d)

instance : CoeFun (ShellField d) (fun _ ↦ Vec d → Mat d) := ⟨fun j ↦ j.1.1⟩

/-- The operator norm on first derivatives. -/
instance (d : ℕ) : NormedAddCommGroup (Vec d →L[ℝ] Mat d) :=
  { (ContinuousLinearMap.toNormedAddCommGroup : NormedAddCommGroup (Vec d →L[ℝ] Mat d)) with
    toAddCommGroup := ContinuousLinearMap.addCommGroup }

instance (d : ℕ) : NormedSpace ℝ (Vec d →L[ℝ] Mat d) :=
  { (ContinuousLinearMap.toNormedSpace : NormedSpace ℝ (Vec d →L[ℝ] Mat d)) with
    toModule := ContinuousLinearMap.module }

/-- The operator norm on second derivatives. -/
instance (d : ℕ) : NormedAddCommGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  { (ContinuousLinearMap.toNormedAddCommGroup :
      NormedAddCommGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) with
    toAddCommGroup := ContinuousLinearMap.addCommGroup }

instance (d : ℕ) : NormedSpace ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  { (ContinuousLinearMap.toNormedSpace : NormedSpace ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) with
    toModule := ContinuousLinearMap.module }

namespace ShellField

/-- The translate `x ↦ j(x + z)`. -/
def translate (z : Vec d) (j : ShellField d) : ShellField d :=
  let τ : C(Vec d, Vec d) := ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩
  ⟨(j.1.1.comp τ, (j.1.2.1.comp τ, j.1.2.2.comp τ)), by
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x i k ↦ j.2.2.2 (x + z) i k⟩
    · exact (j.2.1 (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · exact (j.2.2.1 (x + z)).comp x ((hasFDerivAt_id x).add_const z)⟩

/-- The negated shell `-j`. -/
def negate (j : ShellField d) : ShellField d :=
  ⟨((⟨fun M ↦ (-1 : ℝ) • M, continuous_id.const_smul (-1 : ℝ)⟩ : C(Mat d, Mat d)).comp j.1.1,
    ((⟨fun D ↦ (-1 : ℝ) • D, continuous_id.const_smul (-1 : ℝ)⟩ :
        C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d)).comp j.1.2.1,
      (⟨fun H ↦ (-1 : ℝ) • H, continuous_id.const_smul (-1 : ℝ)⟩ :
        C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d), Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp j.1.2.2)),
    by
      refine ⟨fun x ↦ (j.2.1 x).const_smul (-1 : ℝ), fun x ↦ (j.2.2.1 x).const_smul (-1 : ℝ),
        fun x i k ↦ ?_⟩
      change (-1 : ℝ) * j x i k = -((-1 : ℝ) * j x k i)
      rw [j.2.2.2 x i k, mul_neg]⟩

/-- The map `x ↦ R x`. -/
def matVecCLM (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

/-- The conjugation `M ↦ Rᵀ M R`. -/
def conjugateCLM (R : Mat d) : Mat d →L[ℝ] Mat d :=
  ⟨{ toFun := fun M ↦ R.transpose * M * R
     map_add' := fun M N ↦ by rw [Matrix.mul_add, Matrix.add_mul]
     map_smul' := fun c M ↦ by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] },
    LinearMap.continuous_of_finiteDimensional _⟩

/-- The rotated derivative `D ↦ (v ↦ Rᵀ D(Rv) R)`. -/
def rotateDerivCLM (R : Mat d) : (Vec d →L[ℝ] Mat d) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Mat d) (Mat d) (conjugateCLM R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Mat d)).flip (matVecCLM R))

/-- The rotated second derivative `H ↦ (u ↦ rotateDerivCLM R (H (R u)))`. -/
def rotateSecondDerivCLM (R : Mat d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ] (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] Mat d)
      (rotateDerivCLM R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Vec d →L[ℝ] Mat d)).flip (matVecCLM R))

/-- The signed-permutation conjugate `x ↦ Rᵀ j(Rx) R`, with its derivatives. -/
def rotate (R : Mat d) (j : ShellField d) : ShellField d :=
  let ρ : C(Vec d, Vec d) := ⟨matVecCLM R, (matVecCLM R).continuous⟩
  ⟨((⟨conjugateCLM R, (conjugateCLM R).continuous⟩ : C(Mat d, Mat d)).comp (j.1.1.comp ρ),
    ((⟨rotateDerivCLM R, (rotateDerivCLM R).continuous⟩ :
        C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d)).comp (j.1.2.1.comp ρ),
      (⟨rotateSecondDerivCLM R, (rotateSecondDerivCLM R).continuous⟩ :
        C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d), Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp
        (j.1.2.2.comp ρ))),
    by
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x i k ↦ ?_⟩
    · exact (conjugateCLM R).hasFDerivAt.comp x
        ((j.2.1 (matVecCLM R x)).comp x (matVecCLM R).hasFDerivAt)
    · exact (rotateDerivCLM R).hasFDerivAt.comp x
        ((j.2.2.1 (matVecCLM R x)).comp x (matVecCLM R).hasFDerivAt)
    · have h : (R.transpose * j (matVecCLM R x) * R).transpose =
          -(R.transpose * j (matVecCLM R x) * R) := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
          ← Matrix.mul_assoc, show (j (matVecCLM R x)).transpose = -j (matVecCLM R x) from
            Matrix.ext fun a b ↦ (j.2.2.2 _ b a), Matrix.mul_neg, Matrix.neg_mul]
      exact congrFun (congrFun h k) i⟩

end ShellField

/-! ## 3. Regular coefficient fields -/

/-- Regular matrix fields: every entry is measurable and locally integrable. -/
def RegField (d : ℕ) :=
  { a : Vec d → Mat d //
    (∀ i j, Measurable fun x ↦ a x i j) ∧ ∀ i j, LocallyIntegrable (fun x ↦ a x i j) volume }

/-- Test functions: measurable, bounded and compactly supported. -/
def IsProbe (φ : Vec d → ℝ) : Prop :=
  Measurable φ ∧ (∃ C : ℝ, ∀ x, |φ x| ≤ C) ∧ HasCompactSupport φ

/-- The σ-algebra on regular fields generated by point evaluations and by the entry tests
`a ↦ ∫ aᵢⱼ φ` against test functions. -/
instance (d : ℕ) : MeasurableSpace (RegField d) :=
  MeasurableSpace.comap Subtype.val MeasurableSpace.pi ⊔
    MeasurableSpace.generateFrom
      {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧ ∃ t : Set ℝ, MeasurableSet t ∧
        s = (fun a : RegField d ↦ ∫ x, a.1 x i j * φ x) ⁻¹' t}

/-- Spatial translation `(z +ᵥ a)(x) = a(x + z)`. -/
instance (d : ℕ) : AddAction (Vec d) (RegField d) where
  vadd z a := ⟨fun x ↦ a.1 (x + z), fun i j ↦ (a.2.1 i j).comp (measurable_add_const z),
    fun i j ↦ by
      refine (locallyIntegrable_map_homeomorph (Homeomorph.addRight z)
        (f := fun x ↦ a.1 x i j) (μ := volume)).mp ?_
      rw [show Measure.map (Homeomorph.addRight z) volume = volume from
        (measurePreserving_add_right volume z).map_eq]
      exact a.2.2 i j⟩
  zero_vadd a := Subtype.ext (funext fun x ↦ congrArg a.1 (add_zero x))
  add_vadd z w a := Subtype.ext (funext fun x ↦ congrArg a.1 (add_assoc x z w).symm)

/-- A continuous matrix field as a regular field. -/
def RegField.ofContinuous (a : C(Vec d, Mat d)) : RegField d :=
  ⟨a, fun i j ↦ (a.continuous.matrix_elem i j).measurable,
    fun i j ↦ (a.continuous.matrix_elem i j).locallyIntegrable⟩

/-- The restriction `1_U a` of a regular field to a measurable set `U`. -/
def RegField.restrict (U : Set (Vec d)) (hU : MeasurableSet U) (a : RegField d) : RegField d :=
  ⟨U.indicator a.1,
    fun i j ↦ by
      rw [show (fun x ↦ U.indicator a.1 x i j) = U.indicator (fun x ↦ a.1 x i j) from
        (Set.indicator_comp_of_zero (g := fun M : Mat d ↦ M i j) rfl).symm]
      exact (a.2.1 i j).indicator hU,
    fun i j ↦ by
      rw [show (fun x ↦ U.indicator a.1 x i j) = U.indicator (fun x ↦ a.1 x i j) from
        (Set.indicator_comp_of_zero (g := fun M : Mat d ↦ M i j) rfl).symm]
      exact (a.2.2 i j).indicator hU⟩

/-! ## 4. The shell law and its assumptions -/

/-- The law of the shell `jₙ`. -/
def shellMarginalLaw (P : ProbabilityMeasure (ℕ → ShellField d)) (n : ℕ) :
    ProbabilityMeasure (ShellField d) :=
  P.map fun F ↦ F n

/-- Standing assumptions: `d ≥ 2`, and every shell is stationary under real translations. -/
structure ShellLawPrefix (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) : Prop where
  dimension : 2 ≤ d
  stationary : ∀ (n : ℕ) (z : Vec d),
    Measure.map (ShellField.translate z) (shellMarginalLaw P n).toMeasure =
      (shellMarginalLaw P n).toMeasure

/-- (J1) The shell `jₙ` has range of dependence `3ⁿ √d`: the restrictions of `jₙ` to measurable
sets at distance at least `3ⁿ √d` are independent. -/
structure ShellLawJ1Restriction (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) :
    Prop where
  restriction_range_dependence : ∀ (n : ℕ) (U V : Set (Vec d))
    (hU : MeasurableSet U) (hV : MeasurableSet V),
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → (3 : ℝ) ^ n * Real.sqrt d ≤ vecNorm (x - y)) →
      Indep
        (MeasurableSpace.comap (fun j : ShellField d ↦
          RegField.restrict U hU (RegField.ofContinuous j.1.1)) inferInstance)
        (MeasurableSpace.comap (fun j : ShellField d ↦
          RegField.restrict V hV (RegField.ofContinuous j.1.1)) inferInstance)
        (shellMarginalLaw P n).toMeasure

/-- (J2) The shells are independent. -/
structure ShellLawJ2 (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) : Prop where
  independent : iIndepFun (fun n : ℕ ↦ fun F : ℕ → ShellField d ↦ F n) P.toMeasure

/-- Unit vectors and the zero vector index the supremum defining an induced norm. -/
abbrev UnitBall (d : ℕ) := {v : Vec d // vecNorm v ≤ 1}

/-- The induced norm `sup_{|v| ≤ 1} |D v|` of a matrix-valued linear map. -/
def derivNorm (D : Vec d →L[ℝ] Mat d) : ℝ :=
  sSup (Set.range fun o : Option (UnitBall d) ↦
    match o with | none => 0 | some v => matrixOperatorNorm (D v.1))

/-- The twice-induced norm `sup_{|u| ≤ 1} ‖H u‖` of a second derivative. -/
def secondDerivNorm (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) : ℝ :=
  sSup (Set.range fun o : Option (UnitBall d) ↦
    match o with | none => 0 | some u => derivNorm (H u.1))

/-- Points of the open cube `□ₙ = (-3ⁿ/2, 3ⁿ/2)^d`. -/
abbrev CubePoint (d n : ℕ) :=
  {x : Vec d // ∀ i, (((0 : ℤ) : ℝ) - 1 / 2) * (3 : ℝ) ^ (n : ℤ) < x i ∧
    x i < (((0 : ℤ) : ℝ) + 1 / 2) * (3 : ℝ) ^ (n : ℤ)}

/-- The observable of (J3):
`‖jₙ‖_{L∞(□ₙ)} + √d 3ⁿ ‖∇jₙ‖_{L∞(□ₙ)} + d 3²ⁿ ‖∇²jₙ‖_{L∞(□ₙ)}`. -/
def j3Observable (d n : ℕ) (j : ShellField d) : ℝ :=
  sSup (Set.range fun o : Option (CubePoint d n) ↦
      match o with | none => 0 | some x => matrixOperatorNorm (j x.1)) +
    (Real.sqrt d * (3 : ℝ) ^ n) *
      sSup (Set.range fun o : Option (CubePoint d n) ↦
        match o with | none => 0 | some x => derivNorm (j.1.2.1 x.1)) +
    ((d : ℝ) * (3 : ℝ) ^ (2 * n)) *
      sSup (Set.range fun o : Option (CubePoint d n) ↦
        match o with | none => 0 | some x => secondDerivNorm (j.1.2.2 x.1))

/-- (J3) Gaussian tail of the shell regularity on its cube. -/
structure ShellLawJ3 (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) : Prop where
  gaussian_tail : ∀ (n : ℕ) (t : ℝ), 1 ≤ t →
    P.toMeasure {F : ℕ → ShellField d | t < j3Observable d n (F n)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2)))

/-- (J4) The joint law of the shells is invariant under signed-permutation conjugation and under
negation. -/
structure ShellLawJ4 (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) : Prop where
  hyperoctahedral : ∀ R : Mat d, IsSignedPermutationMatrix R →
    P.map (fun F n ↦ (F n).rotate R) = P
  negation : P.map (fun F n ↦ (F n).negate) = P

/-! ## 5. The stationary block response behind `c⋆` -/

section Stationary

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
  {μ : Measure Ω} [VAddInvariantMeasure (Vec d) Ω μ]

/-- The Koopman isometry `φ ↦ φ(x +ᵥ ·)` of `L²(μ)`. -/
def koopman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : Vec d) :
    Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (x +ᵥ ·) (measurePreserving_vadd x μ)

/-- `F ∈ L²(μ; ℝ^d)` is the horizontal gradient of `φ ∈ L²(μ)`: for each `i`, `F_i` is the
derivative at `0` of `t ↦ φ(t eᵢ +ᵥ ·)` in `L²(μ)`. -/
def HasHorizontalGradient (φ : Lp ℝ 2 μ) (F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) : Prop :=
  ∀ i : Fin d, HasDerivAt (fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ)
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d ↦ ℝ) i).compLpL 2 μ F) 0

/-- `∇Δ⁻¹∇·`: the orthogonal projection of `L²(μ; ℝ^d)` onto the closed span of the horizontal
gradients (the stationary potential fields). -/
def potentialProjection :
    Lp (EuclideanSpace ℝ (Fin d)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
  (Submodule.span ℝ {F | ∃ φ, HasHorizontalGradient (μ := μ) φ F}).topologicalClosure.starProjection

end Stationary

/-- The law of the block field `∑_{n < k ≤ m} jₖ` on regular fields. -/
def blockLaw (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ) : Measure (RegField d) :=
  P.toMeasure.map fun F ↦ RegField.ofContinuous (∑ k ∈ Finset.Ioc n m, (F k).1.1)

/-- (J5) Nondegeneracy with the constants `c⋆` and `K`: for every block `(n, m]` and unit vector
`e`, the energy `|∇Δ⁻¹∇·(a e)(0)|²` of the stationary response to the forcing `a(0) e`, `a` the
block field, is within `K` of `c⋆ (log 3) (m - n)`. -/
structure ShellLawJ5 (d : ℕ) (P : ProbabilityMeasure (ℕ → ShellField d)) (cStar K : ℝ) :
    Prop where
  cStar_pos : 0 < cStar
  K_pos : 0 < K
  nondegenerate : ∀ n m : ℕ, n < m → ∀ e : Vec d, vecNorm e = 1 →
    ∀ [MeasurableConstVAdd (Vec d) (RegField d)]
      [VAddInvariantMeasure (Vec d) (RegField d) (blockLaw P n m)]
      (h : MemLp (fun a : RegField d ↦ (WithLp.toLp 2 (Matrix.mulVec (a.1 0) e) : EuclideanSpace ℝ (Fin d)))
        2 (blockLaw P n m)),
      |‖potentialProjection (h.toLp _)‖ ^ 2 - cStar * Real.log 3 * ((m - n : ℕ) : ℝ)| ≤ K

/-! ## 6. The coefficient field and the diffusion -/

/-- The recentred coefficient field `ν Id + (k − k(0))`, `k = ∑ₙ jₙ`
(a `tsum`, with value `0` where the series does not converge). -/
def fullCoefficientRecentered (nu : ℝ) (ω : ℕ → ShellField d) (x : Vec d) : Mat d :=
  nu • (1 : Mat d) + ∑' n : ℕ, (ω n x - ω n 0)

/-- The divergence-form operator `c ∇·(a∇φ)(x) = c ∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ ∂ⱼ φ)(x)`. -/
def divForm (c : ℝ) (a : CoeffField d) (φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  c * ∑ i : Fin d,
    fderiv ℝ (fun y ↦ ∑ j : Fin d, a y i j * fderiv ℝ φ y (Pi.single j 1)) x (Pi.single i 1)

/-- A jointly measurable semigroup of sub-Markov kernels `S t`, `t ≥ 0`. -/
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  /-- The transition kernel at time `t`. -/
  kernel : ℝ≥0 → Kernel α α
  measurable_kernel : Measurable fun p : ℝ≥0 × α ↦ kernel p.1 p.2
  kernel_zero : kernel 0 = Kernel.id
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  isSubMarkovKernel : ∀ t x, kernel t x Set.univ ≤ 1

namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

instance : CoeFun (SubMarkovKernelSemigroup α) (fun _ ↦ ℝ≥0 → Kernel α α) := ⟨kernel⟩

/-- Every transition law is a probability measure. -/
def IsConservative (S : SubMarkovKernelSemigroup α) : Prop := ∀ t x, S t x Set.univ = 1

/-- `S` maps `C₀` into `C₀`: each `x ↦ ∫ f d(S t x)` is continuous and vanishes at infinity. -/
def MapsC0 (S : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t (f : C₀(α, ℝ)), Continuous (fun x ↦ ∫ y, f y ∂S t x) ∧
    Tendsto (fun x ↦ ∫ y, f y ∂S t x) (cocompact α) (𝓝 0)

/-- The `C₀` function `S_t f = ∫ f d(S t ·)`. -/
def c0KernelIntegral (S : SubMarkovKernelSemigroup α) (hC0 : S.MapsC0) (t : ℝ≥0)
    (f : C₀(α, ℝ)) : C₀(α, ℝ) where
  toFun x := ∫ y, f y ∂S t x
  continuous_toFun := (hC0 t f).1
  zero_at_infty' := (hC0 t f).2

end SubMarkovKernelSemigroup

/-- `S` is a conservative Feller semigroup on `C₀(ℝ^d)` (strongly continuous `t ↦ S_t f`) whose
generator is `∇·(a∇·)` on `C² ∩ C₀`: for every `u ∈ C₀ ∩ C²` with `∇·(a∇u) = v ∈ C₀`,
`t⁻¹ (S_t u − u) → v` in `C₀` as `t → 0⁺`. -/
def IsDivergenceFormFeller (a : CoeffField d) (S : SubMarkovKernelSemigroup (Vec d)) : Prop :=
  S.IsConservative ∧ ∃ hC0 : S.MapsC0, (∀ f, Continuous fun t ↦ S.c0KernelIntegral hC0 t f) ∧
    ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 ⇑u → (∀ x, v x = divForm 1 a ⇑u x) →
      Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • (S.c0KernelIntegral hC0 t u - u)) (𝓝[>] 0) (𝓝 v)

/-! ## 7. Paths and finite-dimensional distributions -/

/-- Continuous paths `[0, ∞) → α`, with the compact-open topology. -/
abbrev ContinuousPath (α : Type*) [TopologicalSpace α] := C(ℝ≥0, α)

/-- The Borel σ-algebra of the compact-open topology. -/
scoped instance (α : Type*) [TopologicalSpace α] : MeasurableSpace (ContinuousPath α) := borel _

/-- Strictly increasing families of `n` times. -/
abbrev OrderedTimes (n : ℕ) := Fin n ↪o ℝ≥0

/-- The later times, shifted so that the first time becomes `0`. -/
def OrderedTimes.relativeTail {n : ℕ} (τ : OrderedTimes (n + 1)) : OrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ τ i.succ - τ 0) fun _ _ hij ↦
    tsub_lt_tsub_right_of_le (τ.monotone (Fin.zero_le _)) (τ.strictMono (Fin.strictMono_succ hij))

theorem measurable_finCons {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦ @Fin.cons n (fun _ ↦ α) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The law of `(X_{τ 0}, …, X_{τ (n-1)})` for transition kernels `κ`: sample at the first
time, then iterate along the increments. -/
def finiteTimeKernel {α : Type*} [MeasurableSpace α] (κ : ℝ≥0 → Kernel α α) :
    {n : ℕ} → OrderedTimes n → Kernel α (Fin n → α)
  | 0, _ => Kernel.const α (Measure.dirac Fin.elim0)
  | n + 1, τ =>
      Kernel.mapOfMeasurable (κ (τ 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel κ τ.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ ↦ α) z.1 z.2) measurable_finCons

/-- The finite-dimensional distribution at the times of `I`, indexed by `I`. -/
def finiteSetKernel {α : Type*} [MeasurableSpace α] (κ : ℝ≥0 → Kernel α α) (I : Finset ℝ≥0) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel κ (I.orderEmbOfFin rfl))
    (fun path t ↦ path ((I.orderIsoOfFin rfl).symm t))
    (measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t))

/-- `Q x` is a probability law on continuous paths with the finite-dimensional distributions of
the transition kernels `κ` started at `x`, for every `x`. -/
def IsContinuousPathLaw (κ : ℝ≥0 → Kernel (Vec d) (Vec d))
    (Q : Vec d → Measure (ContinuousPath (Vec d))) : Prop :=
  ∀ x, IsProbabilityMeasure (Q x) ∧
    ∀ I : Finset ℝ≥0, (Q x).map (fun path (t : I) ↦ path t) = finiteSetKernel κ I x

/-- The heat kernel `N(x, t Id)`: the image of the standard Gaussian vector under
`z ↦ x + √t z`. -/
def heatKernel (d : ℕ) (t : ℝ≥0) : Kernel (Vec d) (Vec d) :=
  Kernel.comap
    ((Kernel.id ×ₖ Kernel.const (ℝ≥0 × Vec d) (Measure.pi fun _ : Fin d ↦ gaussianReal 0 1)).map
      (fun q : (ℝ≥0 × Vec d) × Vec d ↦ q.1.2 + Real.sqrt q.1.1 • q.2))
    (fun x : Vec d ↦ (t, x)) (measurable_const.prodMk measurable_id)

/-- The rescaled path `t ↦ a ω(c t)`. -/
def scalePath (a : ℝ) (c : ℝ≥0) (ω : ContinuousPath (Vec d)) : ContinuousPath (Vec d) :=
  (ContinuousMap.mk (fun x : Vec d ↦ a • x) (continuous_const_smul a)).comp
    (ω.comp ⟨fun t ↦ c * t, continuous_const.mul continuous_id⟩)

/-! ## 8. Theorem A -/

/-- **Theorem A** (quenched superdiffusive invariance principle). For `ν ∈ (0, 1]`, `c⋆ > 0` and
`K`, and every shell law `P` satisfying the standing assumptions and (J1)–(J5)
(standard Brownian motion exists: the heat kernels have a continuous-path law `W`):
* for `P`-a.e. `ω` a diffusion with generator `∇·(ν Id + k − k(0))∇` exists (a semigroup `S`
  and continuous-path laws `Q`), and for `P`-a.e. `ω`, every such `S`, `Q`, starting point
  `x₀` and bounded continuous `F` on paths, `E_{Q x₀}[F(|log ε²|^{-1/4} ε X_{·/ε²})]` converges
  as `ε → 0⁺` to `E[F(√(2 c⋆^{1/2}) W)]`, `W` a standard Brownian motion (the law `W 0` of any
  continuous-path law of the heat kernels started at `0`);
* for `δ ∈ (0, 1/4)`, `β ∈ (0, 4δ)` there is `C` such that for `t ≥ 10` the quenched second
  moment `E⁰|X_t|²` is integrable and
  `P(|t⁻¹ E⁰|X_t|² − 2 d c⋆^{1/2} (log t)^{1/2}| + t⁻¹ |E⁰ X_t|² > C (log t)^{1/4+δ})
  ≤ C exp(−C⁻¹ (log t)^β)`, and for `p ≥ 1` the annealed `L^p` norm of the same quantity is
  at most `C_p (log t)^{1/4+δ}`. -/
theorem theoremA (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∃ W : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw (heatKernel d) W) ∧
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          (∀ P : ProbabilityMeasure (ℕ → ShellField d),
            ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
            (∀ᵐ ω ∂P.toMeasure, ∃ S : SubMarkovKernelSemigroup (Vec d),
                IsDivergenceFormFeller (fullCoefficientRecentered nu ω) S ∧
                  ∃ Q : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw S Q) ∧
            ∀ᵐ ω ∂P.toMeasure,
              ∀ (S : SubMarkovKernelSemigroup (Vec d))
                (Q : Vec d → Measure (ContinuousPath (Vec d))),
                IsDivergenceFormFeller (fullCoefficientRecentered nu ω) S →
                IsContinuousPathLaw S Q →
                ∀ (x₀ : Vec d) (F : BoundedContinuousFunction (ContinuousPath (Vec d)) ℝ)
                  (W : Vec d → Measure (ContinuousPath (Vec d))),
                  IsContinuousPathLaw (heatKernel d) W →
                  Tendsto
                    (fun ε : ℝ ↦ ∫ w, F (scalePath
                        (|Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε) ((ε ^ 2)⁻¹).toNNReal w)
                      ∂(Q x₀))
                    (𝓝[>] 0)
                    (𝓝 (∫ w, F (scalePath (Real.sqrt (2 * Real.sqrt cStar)) 1 w) ∂(W 0)))) ∧
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
            ∃ C : ℝ, 1 ≤ C ∧
              (∀ P : ProbabilityMeasure (ℕ → ShellField d),
                ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
                ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
                ∀ S : (ℕ → ShellField d) → SubMarkovKernelSemigroup (Vec d),
                  (∀ᵐ ω ∂P.toMeasure,
                    IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω)) →
                  ∀ t : ℝ, 10 ≤ t →
                    (∀ᵐ ω ∂P.toMeasure,
                      Integrable (fun y ↦ vecNormSq y) ((S ω) t.toNNReal (0 : Vec d))) ∧
                    P.toMeasure
                        {ω | C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
                            |(1 / t) * (∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d))) -
                                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                              (1 / t) * vecNormSq (∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β)))) ∧
              ∀ p : ℝ, 1 ≤ p →
                ∃ Cp : ℝ, 1 ≤ Cp ∧
                  ∀ P : ProbabilityMeasure (ℕ → ShellField d),
                    ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
                    ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
                    ∀ S : (ℕ → ShellField d) → SubMarkovKernelSemigroup (Vec d),
                      (∀ᵐ ω ∂P.toMeasure,
                        IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω)) →
                      ∀ t : ℝ, 10 ≤ t →
                        AEMeasurable (fun ω ↦ ∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d)))
                            P.toMeasure ∧
                          AEMeasurable (fun ω ↦ ∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))
                            P.toMeasure ∧
                          (∫⁻ ω, ENNReal.ofReal
                                (|(1 / t) * (∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d))) -
                                      2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
                                  ((1 / t) * vecNormSq
                                    (∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))) ^ p)
                              ∂P.toMeasure) ^ (1 / p) ≤
                            ENNReal.ofReal (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)) := by
  sorry

end

end SuperdiffusionCLT.StatementAudit.TheoremA
