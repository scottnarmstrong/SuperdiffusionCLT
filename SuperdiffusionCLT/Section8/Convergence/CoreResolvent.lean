/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Trajectory.WeakConvergence

/-!
# Strong resolvent convergence from generator convergence on a core

This module supplies the link of Kallenberg's Theorem 19.25 that the manuscript uses just before
Proposition `p.generators`: convergence of generators along a core forces strong convergence of
the resolvents, and hence (through the Trotter--Kato theorem of `MarkovProcess`) convergence of
the semigroups and of the path laws of the associated Feller processes.

## The statement

Let `S i` be strongly continuous contraction semigroups on a Banach space `E`, indexed along a
filter `l`, and let `S'` be one more such semigroup, with generator `L'`.  Fix a positive shift
`mu` and a set `D` of vectors of the generator domain of `S'` which is a **core at `mu`**, in the
sense that the set `(mu - L') D` is dense in `E`.  Suppose that every `u ∈ D` admits
approximants `w i` in the generator domains of the `S i` with `w i → u` and
`L_i (w i) → L' u`.  Then `(S i).resolvent mu f → S'.resolvent mu f` for every `f ∈ E`
(`tendsto_resolvent_of_tendsto_generator`).

## The core hypothesis

The hypothesis is stated in the **range-density** form `Dense ((mu - L') '' D)`, which is what the
argument consumes and what the phrase "standard core" provides.  The usual definition of a core --
a subspace `D` of the domain whose graph closure is the whole graph of the generator -- implies it:
for `f ∈ E` the vector `u = R'_mu f` lies in the domain with `(mu - L') u = f`, and approximating
`u` in the graph norm by elements of `D` approximates `f = (mu - L') u` in `E`.  The converse also
holds for the generator of a contraction semigroup, but neither implication is proved here: only
the range-density form is used, and it is the form a concrete core is verified in.

The hypothesis is satisfiable, and degenerates as follows: taking `D` to be the whole generator
domain the set `(mu - L') D` is *all* of `E`, because the resolvent is a right inverse of
`mu - L'` there.  A core is a subset small enough to be checked by hand and still large enough
for its image to be dense.

## Main results

* `tendsto_apply_of_dense_of_opNorm_le`: a uniformly bounded family of continuous linear maps that
  converges pointwise on a dense set converges pointwise everywhere.
* `tendsto_resolvent_apply_of_tendsto_generator`: the one-vector step, `R_i mu ((mu - L') u) → u`.
* `tendsto_resolvent_of_tendsto_generator`: strong convergence of the resolvents.
* `tendsto_operator_of_tendsto_generator`: the resulting convergence of the semigroups at a fixed
  time.

Nothing is asserted about semigroups on varying Banach spaces (Trotter--Kurtz proper), about
non-contractive families, or about the construction of the approximants `w i`; in the marginal
superdiffusion application the latter is the content of Proposition `p.generators` and is Section
8 material.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Topology
open MarkovProcess
open MarkovProcess.Semigroup
open scoped NNReal ZeroAtInfty

noncomputable section

section DenseExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {iota : Type*} {l : Filter iota}

/-- **Pointwise convergence extends from a dense set to the whole space for a uniformly bounded
family.**  If `‖T i‖ ≤ C` for every `i`, if `‖T'‖ ≤ C`, and if `T i y → T' y` for every `y` of a
dense set `D`, then `T i x → T' x` for every `x`.  This is the three-epsilon argument behind
`MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one`, with the limit an arbitrary bounded
operator instead of the identity and with an arbitrary uniform bound instead of `1`.

The bound `hT'` on the limit is redundant when `l` is `NeBot`, where it follows from `hT`, `hD`
and `hcore`; it is kept because every consumer here has it for free. -/
theorem tendsto_apply_of_dense_of_opNorm_le {C : ℝ} (T : iota → E →L[ℝ] F) (T' : E →L[ℝ] F)
    (hT : ∀ i, ‖T i‖ ≤ C) (hT' : ‖T'‖ ≤ C) {D : Set E} (hD : Dense D)
    (hcore : ∀ y ∈ D, Tendsto (fun i ↦ T i y) l (𝓝 (T' y))) (x : E) :
    Tendsto (fun i ↦ T i x) l (𝓝 (T' x)) := by
  have hC : (0 : ℝ) ≤ C := le_trans (norm_nonneg T') hT'
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hden : (0 : ℝ) < 3 * (C + 1) := by positivity
  have hdelta : (0 : ℝ) < eps / (3 * (C + 1)) := div_pos heps hden
  obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.mp (hD x) _ hdelta
  have hC1 : (0 : ℝ) < C + 1 := by linarith only [hC]
  have hCdelta : C * (eps / (3 * (C + 1))) ≤ eps / 3 := by
    have key : C * (eps / (3 * (C + 1))) = eps / 3 * (C / (C + 1)) := by
      rw [div_mul_div_comm, mul_div_assoc', mul_comm C eps]
    have hfrac : C / (C + 1) ≤ 1 := by
      rw [div_le_one hC1]
      linarith only []
    rw [key]
    calc eps / 3 * (C / (C + 1)) ≤ eps / 3 * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = eps / 3 := mul_one _
  filter_upwards [Metric.tendsto_nhds.mp (hcore y hyD) (eps / 3) (by positivity)] with i hi
  have h1 : dist (T i x) (T i y) ≤ eps / 3 := by
    refine le_trans ((T i).dist_le_opNorm x y) (le_trans ?_ hCdelta)
    exact mul_le_mul (hT i) hxy.le dist_nonneg hC
  have h3 : dist (T' y) (T' x) ≤ eps / 3 := by
    refine le_trans (T'.dist_le_opNorm y x) (le_trans ?_ hCdelta)
    refine mul_le_mul hT' ?_ dist_nonneg hC
    rw [dist_comm]
    exact hxy.le
  have htri : dist (T i x) (T' x) ≤
      dist (T i x) (T i y) + dist (T i y) (T' y) + dist (T' y) (T' x) :=
    dist_triangle4 _ _ _ _
  linarith only [h1, h3, hi, htri]

end DenseExtension

section CoreResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {iota : Type*} {l : Filter iota}

/-- **The one-vector step.**  Let `u` be a vector of the generator domain of `S'` and let `w i` be
vectors of the generator domains of the `S i` with `w i → u` and `L_i (w i) → L' u`.  Then the
resolvents of the `S i` applied to `(mu - L') u` converge to `u`.

The identity behind it is
`R_i mu ((mu - L') u) - w i = R_i mu ((mu - L') u - (mu - L_i) (w i))`,
whose right-hand side is an operator of norm at most `mu⁻¹` applied to a vector tending to
zero. -/
theorem tendsto_resolvent_apply_of_tendsto_generator
    {S : iota → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} (mu : PositiveShift)
    (u : S'.generatorDomain) (w : (i : iota) → (S i).generatorDomain)
    (hw : Tendsto (fun i ↦ ((w i : E))) l (𝓝 (u : E)))
    (hLw : Tendsto (fun i ↦ (S i).generator (w i)) l (𝓝 (S'.generator u))) :
    Tendsto (fun i ↦ (S i).resolvent mu ((mu : ℝ) • (u : E) - S'.generator u)) l (𝓝 (u : E)) := by
  have hgzero : Tendsto (fun i ↦ ((mu : ℝ) • (u : E) - S'.generator u) -
      ((mu : ℝ) • ((w i : E)) - (S i).generator (w i))) l (𝓝 0) := by
    have h : Tendsto (fun i ↦ (mu : ℝ) • ((w i : E)) - (S i).generator (w i)) l
        (𝓝 ((mu : ℝ) • (u : E) - S'.generator u)) := (hw.const_smul (mu : ℝ)).sub hLw
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (mu : ℝ) • (u : E) - S'.generator u) (f := l)).sub h
  have hnorm : ∀ i, ‖(S i).resolvent mu (((mu : ℝ) • (u : E) - S'.generator u) -
      ((mu : ℝ) • ((w i : E)) - (S i).generator (w i)))‖ ≤
      (mu : ℝ)⁻¹ * ‖((mu : ℝ) • (u : E) - S'.generator u) -
        ((mu : ℝ) • ((w i : E)) - (S i).generator (w i))‖ := by
    intro i
    refine le_trans (((S i).resolvent mu).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right ((S i).opNorm_resolvent_le mu) (norm_nonneg _)
  have hres : Tendsto (fun i ↦ (S i).resolvent mu
      (((mu : ℝ) • (u : E) - S'.generator u) -
        ((mu : ℝ) • ((w i : E)) - (S i).generator (w i)))) l (𝓝 0) := by
    refine squeeze_zero_norm hnorm ?_
    simpa only [norm_zero, mul_zero] using
      (tendsto_const_nhds (x := (mu : ℝ)⁻¹) (f := l)).mul hgzero.norm
  have hsplit : ∀ i, (S i).resolvent mu ((mu : ℝ) • (u : E) - S'.generator u) =
      (S i).resolvent mu (((mu : ℝ) • (u : E) - S'.generator u) -
        ((mu : ℝ) • ((w i : E)) - (S i).generator (w i))) + (w i : E) := by
    intro i
    have h1 : (S i).resolvent mu (((mu : ℝ) • (u : E) - S'.generator u) -
        ((mu : ℝ) • ((w i : E)) - (S i).generator (w i))) =
        (S i).resolvent mu ((mu : ℝ) • (u : E) - S'.generator u) -
          (S i).resolvent mu ((mu : ℝ) • ((w i : E)) - (S i).generator (w i)) :=
      map_sub _ _ _
    rw [h1, (S i).resolvent_smul_sub_generator mu (w i)]
    abel
  simpa only [hsplit, zero_add] using hres.add hw

/-- **Strong convergence of the resolvents from convergence of the generators on a core.**  This
is the missing link of Kallenberg's Theorem 19.25.

`D` is a set of vectors of the generator domain of the limit semigroup `S'` whose image under
`mu - L'` is dense in `E` (`hDdense`); this is the range-density form of the statement that `D` is
a core for `L'`.  The approximation hypothesis `happrox` is the abstract form of the conclusion
of the manuscript's Proposition `p.generators`: for every `u ∈ D` there are vectors `w i` in the
generator domains of the approximating semigroups with `w i → u` and `L_i (w i) → L' u`.

The conclusion is strong convergence of the resolvents at the shift `mu`, the hypothesis consumed
by the Trotter--Kato theorem of `MarkovProcess`. -/
theorem tendsto_resolvent_of_tendsto_generator
    {S : iota → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {mu : PositiveShift}
    {D : Set S'.generatorDomain}
    (hDdense : Dense {f : E | ∃ u ∈ D, (mu : ℝ) • (u : E) - S'.generator u = f})
    (happrox : ∀ u ∈ D, ∃ w : (i : iota) → (S i).generatorDomain,
      Tendsto (fun i ↦ ((w i : E))) l (𝓝 (u : E)) ∧
        Tendsto (fun i ↦ (S i).generator (w i)) l (𝓝 (S'.generator u)))
    (f : E) :
    Tendsto (fun i ↦ (S i).resolvent mu f) l (𝓝 (S'.resolvent mu f)) := by
  refine tendsto_apply_of_dense_of_opNorm_le (C := (mu : ℝ)⁻¹) (fun i ↦ (S i).resolvent mu)
    (S'.resolvent mu) (fun i ↦ (S i).opNorm_resolvent_le mu) (S'.opNorm_resolvent_le mu)
    hDdense ?_ f
  rintro y ⟨u, huD, rfl⟩
  obtain ⟨w, hw, hLw⟩ := happrox u huD
  rw [S'.resolvent_smul_sub_generator mu u]
  exact tendsto_resolvent_apply_of_tendsto_generator mu u w hw hLw

/-- **Strong convergence of the semigroups from convergence of the generators on a core**, at a
fixed time. -/
theorem tendsto_operator_of_tendsto_generator
    {S : iota → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {mu : PositiveShift}
    {D : Set S'.generatorDomain}
    (hDdense : Dense {f : E | ∃ u ∈ D, (mu : ℝ) • (u : E) - S'.generator u = f})
    (happrox : ∀ u ∈ D, ∃ w : (i : iota) → (S i).generatorDomain,
      Tendsto (fun i ↦ ((w i : E))) l (𝓝 (u : E)) ∧
        Tendsto (fun i ↦ (S i).generator (w i)) l (𝓝 (S'.generator u)))
    (x : E) (t : NNReal) :
    Tendsto (fun i ↦ (S i) t x) l (𝓝 (S' t x)) :=
  StronglyContinuousContractionSemigroup.tendsto_operator_of_tendsto_resolvent
    (tendsto_resolvent_of_tendsto_generator hDdense happrox) x t

end CoreResolvent

section Feller

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

end Feller

end

end SuperdiffusionCLT.Section8.Convergence
