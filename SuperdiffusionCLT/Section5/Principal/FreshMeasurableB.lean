/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.FreshMeasurable
public import SuperdiffusionCLT.Section5.Response.NeumannMeasurable
public import SuperdiffusionCLT.Section5.Principal.AverageMoment

/-!
# Fresh-shell measurability of the response averages and of the coordinates of `P̂`

For a flux family `a ↦ F a` whose `L²(cu_Kc)` class is measurable, the weak-gradient class of every
selection of the Dirichlet (resp. Neumann) response is measurable
(`pmeas_measurable_gradClass_dirichlet`, `pmeas_measurable_gradClass_neumann`); the cube average
of the gradient is the inner product of that class with the class of a fixed indicator field
(`pmeas_measurable_volumeAverageVec_of_class`). All three statements hold for an arbitrary
`σ`-algebra on the parameter, so with `hshellFlux`, whose pointwise values are fresh-measurable,
the averages `e_D`, `e_N` and the coordinates of `P̂` are measurable for `σ(j_r : m - h < r ≤ m)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)

variable {d : ℕ}

theorem pmeas_matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-! ## The gradient classes, for an arbitrary parameter `σ`-algebra -/

section Classes

variable {α : Type*} [mα : MeasurableSpace α] [NeZero d]

/-- The weak-gradient class of every selection of the cube Dirichlet response of a flux family with
measurable class is measurable, for an arbitrary `σ`-algebra on the parameter. -/
theorem pmeas_measurable_gradClass_dirichlet {Q : TriadicCube d} {F : α → Vec d → Vec d}
    (hFmem : ∀ a, MemVectorL2 (openCubeSet Q) (F a))
    (hFmeas : Measurable fun a => toHilbertVectorL2OfVecField (hFmem a))
    {w : α → H10Function (openCubeSet Q)}
    (hw : ∀ a, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse Q (F a)
      (w a)) :
    Measurable fun a => (w a).toH1Function.gradToHilbertVectorL2 := by
  have hfun : (fun a => (w a).toH1Function.gradToHilbertVectorL2) =
      fun a => SuperdiffusionCLT.Section3.Setup.cubeDirichletGradClass Q
        (toHilbertVectorL2OfVecField (hFmem a)) :=
    funext fun a =>
      SuperdiffusionCLT.Section3.Setup.cubeDirichletGradClass_eq_of_isCubeDirichletResponse
        (hFmem a) (hw a)
  rw [hfun]
  exact (SuperdiffusionCLT.Section3.Setup.continuous_cubeDirichletGradClass Q).measurable.comp
    hFmeas

omit [NeZero d] in
/-- The Neumann analogue of `pmeas_measurable_gradClass_dirichlet` (the cube-average measurability
of the Neumann response is built on it: `pmeas_measurable_volumeAverageVec_of_class`). -/
theorem pmeas_measurable_gradClass_neumann {Q : TriadicCube d} {F : α → Vec d → Vec d}
    (hFmem : ∀ a, MemVectorL2 (openCubeSet Q) (F a))
    (hFmeas : Measurable fun a => toHilbertVectorL2OfVecField (hFmem a))
    {w : α → H1MeanZeroFunction (openCubeSet Q)}
    (hw : ∀ a, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse Q (F a)
      (w a)) :
    Measurable fun a => (w a).toH1Function.gradToHilbertVectorL2 := by
  have hfun : (fun a => (w a).toH1Function.gradToHilbertVectorL2) =
      fun a => SuperdiffusionCLT.Section3.Terms.cubeNeumannGradClass Q
        (toHilbertVectorL2OfVecField (hFmem a)) :=
    funext fun a =>
      SuperdiffusionCLT.Section3.Terms.cubeNeumannGradClass_eq_of_isCubeNeumannResponse
        (hFmem a) (hw a)
  rw [hfun]
  exact (SuperdiffusionCLT.Section3.Terms.continuous_cubeNeumannGradClass Q).measurable.comp
    hFmeas

omit [NeZero d] in
/-- **Cube averages of an `L²(cu_Kc)` family with measurable class are measurable.** The `i`-th
coordinate of the average over a measurable `V ⊆ cu_Kc` is `|V|⁻¹` times the inner product of the
class of the indicator of `V` times `e_i` with the class of the family. -/
theorem pmeas_measurable_volumeAverageVec_of_class {Kc : ℕ} {V : Set (Vec d)}
    (hVU : V ⊆ openCubeSet (originCube d (Kc : ℤ))) (hV : MeasurableSet V)
    {G : α → Vec d → Vec d}
    (hmem : ∀ a, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (G a))
    (hclass : Measurable fun a => toHilbertVectorL2OfVecField (hmem a)) :
    Measurable fun a => volumeAverageVec V (G a) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine Measurable.of_eval fun i => ?_
  have hKmem : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (Set.indicator V (fun _ : Vec d => (fun j => (1 : Mat d) i j : Vec d))) :=
    (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ)
      (continuous_const (y := (fun j => (1 : Mat d) i j : Vec d)))).indicator hV
  have hfun : (fun a => volumeAverageVec V (G a) i) = fun a =>
      (MeasureTheory.volume V).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField hKmem) (toHilbertVectorL2OfVecField (hmem a)) := by
    funext a
    have h1 := SuperdiffusionCLT.Section3.Setup.volumeAverageVec_matVecMul_eq_inner hVU hV
      (fun _ => (1 : Mat d)) (hmem a) i hKmem
    simp only [pmeas_matVecMul_one] at h1
    exact h1
  rw [hfun]
  exact (continuous_inner.measurable.comp (measurable_const.prodMk hclass)).const_mul _

end Classes

/-! ## The responses to the stream flux, for the fresh `σ`-algebra -/

section Responses

variable [NeZero d]

omit [NeZero d] in
/-- A Caratheodory flux family, fresh-measurable at every point, has a fresh-measurable `L²(cu_Kc)`
class. -/
theorem pmeas_measurable_fluxClass_fresh (S : Set ℕ) {Kc : ℕ} {F : ShellSeq d → Vec d → Vec d}
    (hcont : ∀ ω, Continuous (F ω))
    (hmeas : ∀ x, Measurable[shellSigma (d := d) S] fun ω => F ω x) :
    Measurable[shellSigma (d := d) S] fun ω =>
      toHilbertVectorL2OfVecField
        (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ) (hcont ω)) :=
  @SuperdiffusionCLT.Section3.Setup.measurable_toHilbertVectorL2OfVecField_of_measurable
    d (ShellSeq d) (shellSigma (d := d) S) _ _
    (SuperdiffusionCLT.Section3.Setup.measurable_prod_of_continuous_of_measurable
      (mAlpha := shellSigma (d := d) S) hcont hmeas)
    (fun ω => SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ) (hcont ω))

/-- **`e_D`: the cube average of `∇w_D` is fresh-measurable.** For every selection `w_D` of the
Dirichlet response on `cu_Kc` of the flux `hshellFlux`, and every cube `Q` inside `cu_Kc`, the
average of `∇w_D` over `Q` reads only the shells `(m - h, m]`. -/
theorem pmeas_measurable_dirichlet_average_fresh (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (ew : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ew) (wD ω))
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω => volumeAverageVec (cubeSet Q) (wD ω).toH1Function.grad) := by
  have hFmeas := pmeas_measurable_fluxClass_fresh (d := d) (Set.Ioc (m - h) m) (Kc := Kc)
    (F := fun ω => hshellFlux nu P m h ω ew)
    (fun ω => pmeas_continuous_hshellFlux nu P m h ω ew)
    (fun x => pmeas_measurable_hshellFlux_fresh nu P m h ew x)
  have hcl := @pmeas_measurable_gradClass_dirichlet d (ShellSeq d) (shellSigma (d := d)
    (Set.Ioc (m - h) m)) _ (originCube d (Kc : ℤ)) _ _ hFmeas wD hwD
  have hfun : (fun ω : ShellSeq d => volumeAverageVec (cubeSet Q) (wD ω).toH1Function.grad) =
      fun ω => volumeAverageVec (openCubeSet Q) (wD ω).toH1Function.grad :=
    funext fun ω => SuperdiffusionCLT.Section3.ResponseFields.volumeAverageVec_cubeSet_eq_openCubeSet
      Q _
  rw [hfun]
  exact @pmeas_measurable_volumeAverageVec_of_class d (ShellSeq d) (shellSigma (d := d)
    (Set.Ioc (m - h) m)) Kc (openCubeSet Q) hQ (isOpen_openCubeSet Q).measurableSet
    (fun ω => (wD ω).toH1Function.grad)
    (fun ω => (wD ω).toH1Function.grad_memVectorL2) hcl


/-- **`e_N`: the cube average of `∇w_N + hshellFlux e'` is fresh-measurable.** The missing Neumann
cube-average measurability lemma, with the flux term `shom⁻¹ hshell e'` of `gN` included. -/
theorem pmeas_measurable_neumann_average_fresh (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (ew e' : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwN : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ew) (wN ω))
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω => volumeAverageVec (cubeSet Q)
        (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)) := by
  have hFmeas := pmeas_measurable_fluxClass_fresh (d := d) (Set.Ioc (m - h) m) (Kc := Kc)
    (F := fun ω => hshellFlux nu P m h ω ew)
    (fun ω => pmeas_continuous_hshellFlux nu P m h ω ew)
    (fun x => pmeas_measurable_hshellFlux_fresh nu P m h ew x)
  have hcl := @pmeas_measurable_gradClass_neumann d (ShellSeq d) (shellSigma (d := d)
    (Set.Ioc (m - h) m)) (originCube d (Kc : ℤ)) _ _ hFmeas wN hwN
  have hnegcont : ∀ ω : ShellSeq d,
      Continuous (fun x => -hshellFlux nu P m h ω e' x) :=
    fun ω => (pmeas_continuous_hshellFlux nu P m h ω e').neg
  have hNeg := pmeas_measurable_fluxClass_fresh (d := d) (Set.Ioc (m - h) m) (Kc := Kc)
    (F := fun ω x => -hshellFlux nu P m h ω e' x) hnegcont
    (fun x => (pmeas_measurable_hshellFlux_fresh nu P m h e' x).neg)
  have hmemG : ∀ ω : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      ((wN ω).toH1Function.grad - fun x => -hshellFlux nu P m h ω e' x) := fun ω =>
    (wN ω).toH1Function.grad_memVectorL2.sub
      (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ) (hnegcont ω))
  have hclG : Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] fun ω =>
      toHilbertVectorL2OfVecField (hmemG ω) := by
    have hfun : (fun ω : ShellSeq d => toHilbertVectorL2OfVecField (hmemG ω)) = fun ω =>
        toHilbertVectorL2OfVecField (wN ω).toH1Function.grad_memVectorL2 -
          toHilbertVectorL2OfVecField
            (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ)
              (hnegcont ω)) :=
      funext fun ω => toHilbertVectorL2OfVecField_sub _ _
    rw [hfun]
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    exact continuous_sub.measurable.comp (hcl.prodMk hNeg)
  have hfun : (fun ω : ShellSeq d => volumeAverageVec (cubeSet Q)
      (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)) = fun ω =>
      volumeAverageVec (openCubeSet Q)
        ((wN ω).toH1Function.grad - fun x => -hshellFlux nu P m h ω e' x) := by
    funext ω
    rw [SuperdiffusionCLT.Section3.ResponseFields.volumeAverageVec_cubeSet_eq_openCubeSet]
    congr 1
    funext x
    simp only [Pi.sub_apply, sub_neg_eq_add]
  rw [hfun]
  exact @pmeas_measurable_volumeAverageVec_of_class d (ShellSeq d) (shellSigma (d := d)
    (Set.Ioc (m - h) m)) Kc (openCubeSet Q) hQ (isOpen_openCubeSet Q).measurableSet
    _ hmemG hclG

omit [NeZero d] in
theorem pmeas_measurable_matVecMul_apply {S : Set ℕ} {M : ShellSeq d → Mat d}
    {x : ShellSeq d → Vec d}
    (hM : ∀ i j, Measurable[shellSigma (d := d) S] fun ω => M ω i j)
    (hx : ∀ j, Measurable[shellSigma (d := d) S] fun ω => x ω j) (i : Fin d) :
    Measurable[shellSigma (d := d) S] fun ω => matVecMul (M ω) (x ω) i :=
  Finset.measurable_sum _ fun j _ => (hM i j).mul (hx j)

/-- **The coordinates of `P̂_z` are fresh-measurable.** `P̂_z = G_{-hbar_z} P_z` with
`P_z = blockSlope`, `∇w_D`, `∇w_N + shom⁻¹ hshell e'` the Dirichlet and Neumann responses of
`hshellFlux`, for every cube `Q` inside `cu_Kc`. -/
theorem pmeas_measurable_phat_coord_fresh (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (ew e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ew) (wD ω))
    (hwN : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ew) (wN ω))
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)))
    (a : BlockCoord d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω => toFullBlockVec (principalPhat m h Q ω
        (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
          (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x))) a) := by
  have hD := pmeas_measurable_dirichlet_average_fresh nu P m h Kc ew wD hwD Q hQ
  have hN := pmeas_measurable_neumann_average_fresh nu P m h Kc ew e' wN hwN Q hQ
  have hX1 : ∀ j, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] fun ω =>
      (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
        (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)).1 j :=
    fun j => (measurable_const.add ((measurable_pi_apply j).comp hD)).const_smul _
  have hX2 : ∀ j, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] fun ω =>
      (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
        (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)).2 j :=
    fun j => (measurable_const.add ((measurable_pi_apply j).comp hN)).const_smul _
  have hone : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun _ : ShellSeq d => (1 : Mat d) i j := fun _ _ => measurable_const
  have hzero : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun _ : ShellSeq d => (0 : Mat d) i j := fun _ _ => measurable_const
  have hneg : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun ω : ShellSeq d => (-principalGauge m h Q ω) i j :=
    fun i j => (pmeas_measurable_principalGauge_entry_fresh m h Q i j).neg
  cases a with
  | inl i =>
      exact (pmeas_measurable_matVecMul_apply hone hX1 i).add
        (pmeas_measurable_matVecMul_apply hzero hX2 i)
  | inr i =>
      exact (pmeas_measurable_matVecMul_apply hneg hX1 i).add
        (pmeas_measurable_matVecMul_apply hone hX2 i)

end Responses

/-! ## Satisfiability -/

/-- Witness: `d = 2`, the Dirac law at the zero shell sequence, `m = 5`, `h = 2`, `cu_3`, `Q = cu_3`,
and Dirichlet and Neumann responses of `hshellFlux` (which exist, `exists_response_data`):
all the hypotheses hold and the conclusions are the three measurability statements. -/
example (ew e e' : Vec 2) :
    ∃ (wD : ShellSeq 2 → H10Function (openCubeSet (originCube 2 ((3 : ℕ) : ℤ))))
      (wN : ShellSeq 2 → H1MeanZeroFunction (openCubeSet (originCube 2 ((3 : ℕ) : ℤ)))),
      (∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
        (originCube 2 ((3 : ℕ) : ℤ))
        (hshellFlux (1 : ℝ) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 5 2 ω ew)
        (wD ω)) ∧
      (∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube 2 ((3 : ℕ) : ℤ))
        (hshellFlux (1 : ℝ) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 5 2 ω ew)
        (wN ω)) ∧
      Measurable[shellSigma (d := 2) (Set.Ioc (5 - 2) 5)]
        (fun ω => volumeAverageVec (cubeSet (originCube 2 ((3 : ℕ) : ℤ)))
          (wD ω).toH1Function.grad) ∧
      Measurable[shellSigma (d := 2) (Set.Ioc (5 - 2) 5)]
        (fun ω => volumeAverageVec (cubeSet (originCube 2 ((3 : ℕ) : ℤ)))
          (fun x => (wN ω).toH1Function.grad x +
            hshellFlux (1 : ℝ) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 5 2
              ω e' x)) ∧
      ∀ a : BlockCoord 2, Measurable[shellSigma (d := 2) (Set.Ioc (5 - 2) 5)]
        (fun ω => toFullBlockVec (principalPhat 5 2 (originCube 2 ((3 : ℕ) : ℤ)) ω
          (blockSlope (1 : ℝ) (5 - 2) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2)
            (originCube 2 ((3 : ℕ) : ℤ)) e e' (wD ω).toH1Function.grad
            (fun x => (wN ω).toH1Function.grad x +
              hshellFlux (1 : ℝ) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 5 2
                ω e' x))) a) := by
  obtain ⟨wD, wN, hD, hN, _⟩ := exists_response_data (d := 2) le_rfl (1 : ℝ)
    (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 5 2 3 ew
  exact ⟨wD, wN, hD, hN,
    pmeas_measurable_dirichlet_average_fresh _ _ 5 2 3 ew wD hD _ Set.Subset.rfl,
    pmeas_measurable_neumann_average_fresh _ _ 5 2 3 ew e' wN hN _ Set.Subset.rfl,
    pmeas_measurable_phat_coord_fresh _ _ 5 2 3 ew e e' wD wN hD hN _ Set.Subset.rfl⟩


end SuperdiffusionCLT.Section5
