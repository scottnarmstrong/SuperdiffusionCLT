/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Limit
public import SuperdiffusionCLT.Section6.Engine.SolutionLimit
public import SuperdiffusionCLT.Section6.Engine.SolutionLimitB

/-!
# The global limit of truncated solutions

A sequence of globally defined `L²`-bounded functions with gradient fields, which are solutions
on every origin cube below their index and whose increments (and gradient increments) are
summable in `L²` of every origin cube, converges to an entire solution.
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem eb6b_cube_mono {k m : ℕ} (h : k ≤ m) : engCube d k ⊆ engCube d m := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (3 : ℝ) ^ (k : ℤ) ≤ (3 : ℝ) ^ (m : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by exact_mod_cast h)
  have h1 := hx i
  constructor
  · linarith only [h1.1, h3]
  · linarith only [h1.2, h3]

theorem eb6b_ae_cube {k : ℕ} {P : Vec d → Prop} (h : ∀ x ∈ engCube d k, P x) :
    ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (k : ℤ))), P x := by
  have h1 : ∀ᵐ x ∂(volume.restrict (engCube d k)), P x :=
    (ae_restrict_iff' (measurableSet_openCubeSet _)).2 (Filter.Eventually.of_forall h)
  rw [eb6b_vol_eq, Measure.ae_ennreal_smul_measure_iff (by simp)] at h1
  exact h1

theorem eb6b_cubeL2_congr {k : ℕ} {f g : Vec d → ℝ} (h : ∀ x ∈ engCube d k, f x = g x) :
    cubeL2 k f = cubeL2 k g :=
  cubeL2_congr_ae (eb6b_ae_cube h)

theorem eb6b_cubeFlat_congr {k : ℕ} {f g : Vec d → ℝ} (h : ∀ x ∈ engCube d k, f x = g x) :
    cubeFlat k f = cubeFlat k g :=
  cubeFlat_congr_ae (eb6b_ae_cube h)

theorem eb6b_cubeFlat_zero [NeZero d] (k : ℕ) : cubeFlat k (fun _ : Vec d => (0 : ℝ)) = 0 := by
  have := e0b_isProb (d := d) k
  rw [e0b_cubeFlat_eq]
  simp

theorem eb6b_cubeL2_neg (k : ℕ) (f : Vec d → ℝ) : cubeL2 k (fun x => -f x) = cubeL2 k f := by
  unfold cubeL2 cubeLpNorm
  rw [show (fun x => -f x) = -f from rfl, eLpNorm_neg]

theorem eb6b_tendsto_eLpNorm [NeZero d] (K : ℕ) {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF : ∀ m, MemLp (F m) 2 (normalizedCubeMeasure (originCube d (K : ℤ))))
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (K : ℤ))))
    (h : Tendsto (fun m => cubeL2 K (fun x => F m x - f x)) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun x => F m x - f x) 2 (volume.restrict (engCube d K)))
      atTop (𝓝 0) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (((3 : ℝ) ^ K) ^ d) ^ (1 / (2 : ℝ≥0∞)).toReal with hc
  have hcne : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by simp) ENNReal.ofReal_ne_top
  have e : ∀ m, eLpNorm (fun x => F m x - f x) 2 (volume.restrict (engCube d K)) =
      c * ENNReal.ofReal (cubeL2 K (fun x => F m x - f x)) := by
    intro m
    have hd : MemLp (fun x => F m x - f x) 2
        (normalizedCubeMeasure (originCube d (K : ℤ))) := (hF m).sub hf
    rw [eb6b_vol_eq, eLpNorm_smul_measure_of_ne_top (hf := hd.aestronglyMeasurable)
      (by norm_num), smul_eq_mul]
    congr 1
    unfold cubeL2 cubeLpNorm
    rw [ENNReal.ofReal_toReal hd.eLpNorm_ne_top]
  simp_rw [e]
  have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h) (Or.inr hcne)
  simpa using this

/-- A sequence of globally `L²`-bounded functions with gradient fields, solutions on every cube
below their index, with summable increments and gradient increments, has an entire solution
limit. -/
theorem eb6b_entire_limit [NeZero d] {a : CoeffField d} (hGE : GrowthElliptic a)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    {fm : ℕ → Vec d → ℝ} {gm : ℕ → Vec d → Vec d}
    (hmem : ∀ m k : ℕ, MemLp (fm m) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hgmem : ∀ (m k : ℕ) (i : Fin d),
      MemLp (fun x => gm m x i) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hsol : ∀ m K : ℕ, K ≤ m → IsSolOn a (engCube d K) (fm m) (gm m))
    (hsum : ∀ k : ℕ, Summable fun m => cubeL2 k (fun x => fm (m + 1) x - fm m x))
    (hgsum : ∀ (k : ℕ) (i : Fin d),
      Summable fun m => cubeL2 k (fun x => gm (m + 1) x i - gm m x i)) :
    ∃ (f : Vec d → ℝ) (g : Vec d → Vec d),
      (∀ᵐ x ∂volume, Tendsto (fun m => fm m x) atTop (𝓝 (f x))) ∧
      (∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) ∧
        Tendsto (fun m => cubeL2 k (fun x => fm m x - f x)) atTop (𝓝 0)) ∧
      IsEntireSolution a f g := by
  obtain ⟨f, hae, hf⟩ := exists_limit_of_summable_cubeL2 hmem hsum
  have hG : ∀ i : Fin d, ∃ G : Vec d → ℝ, ∀ k : ℕ,
      MemLp G 2 (normalizedCubeMeasure (originCube d (k : ℤ))) ∧
        Tendsto (fun m => cubeL2 k (fun x => gm m x i - G x)) atTop (𝓝 0) := fun i => by
    obtain ⟨G, -, hG⟩ := exists_limit_of_summable_cubeL2 (fm := fun m x => gm m x i)
      (fun m k => hgmem m k i) (fun k => hgsum k i)
    exact ⟨G, fun k => ⟨(hG k).1, (hG k).2.1⟩⟩
  choose G hG using hG
  refine ⟨f, fun x i => G i x, hae, fun k => ⟨(hf k).1, (hf k).2.1⟩, ?_⟩
  have hK : ∀ K : ℕ, IsSolOn a (engCube d K) f (fun x i => G i x) := by
    intro K
    refine IsSolOn.of_tendsto (isOpen_openCubeSet _) (volume_openCubeSet_lt_top _).ne (hell K)
      (um := fun j => fm (j + K)) (gm := fun j => gm (j + K))
      (fun j => hsol _ _ (Nat.le_add_left K j)) ?_ (fun i => ?_)
    · have := eb6b_tendsto_eLpNorm K (F := fm) (fun m => hmem m K) (hf K).1 (hf K).2.1
      exact (Filter.tendsto_add_atTop_iff_nat K).2 this
    · have := eb6b_tendsto_eLpNorm K (F := fun m x => gm m x i) (fun m => hgmem m K i)
        (hG i K).1 (hG i K).2
      exact (Filter.tendsto_add_atTop_iff_nat K).2 this
  intro R hR
  obtain ⟨K, hK'⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  exact IsSolOn.ball_of_cube (hGE R hR) hR hK'.le (hK K)

/-- The flatness of the tail of a sequence converging in `L²(□_k)` is controlled by the
flatness of its increments. -/
theorem eb6b_flat_tail [NeZero d] {k : ℕ} {fm : ℕ → Vec d → ℝ} {L : Vec d → ℝ}
    (hmem : ∀ m, MemLp (fm m) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hL : MemLp L 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hconv : Tendsto (fun m => cubeL2 k (fun x => fm m x - L x)) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha : Summable a) (j : ℕ)
    (hb : ∀ i, cubeFlat k (fun x => fm (j + i + 1) x - fm (j + i) x) ≤ a i) :
    cubeFlat k (fun x => L x - fm j x) ≤ ∑' i, a i := by
  have hpart : ∀ N : ℕ, cubeFlat k (fun x => fm (j + N) x - fm j x) ≤
      ∑ i ∈ Finset.range N, a i := by
    intro N
    induction N with
    | zero => simp [eb6b_cubeFlat_zero]
    | succ N ih =>
      have e : (fun x => fm (j + (N + 1)) x - fm j x) =
          fun x => (fm (j + N + 1) x - fm (j + N) x) + (fm (j + N) x - fm j x) := by
        funext x; simp only [← add_assoc]; ring
      rw [e, Finset.sum_range_succ]
      have h1 : MemLp (fun x => fm (j + N + 1) x - fm (j + N) x) 2
          (normalizedCubeMeasure (originCube d (k : ℤ))) := (hmem _).sub (hmem _)
      have h2 : MemLp (fun x => fm (j + N) x - fm j x) 2
          (normalizedCubeMeasure (originCube d (k : ℤ))) := (hmem _).sub (hmem _)
      have h3 := cubeFlat_add_le h1 h2
      linarith only [h3, ih, hb N]
  have hlim : Tendsto (fun N => ((3 : ℝ)⁻¹) ^ k * cubeL2 k (fun x => fm (j + N) x - L x) +
      ∑ i ∈ Finset.range N, a i) atTop
      (𝓝 (((3 : ℝ)⁻¹) ^ k * 0 + ∑' i, a i)) := by
    refine Tendsto.add (Tendsto.const_mul _ ?_) ha.hasSum.tendsto_sum_nat
    exact hconv.comp (tendsto_atTop_mono (fun N => Nat.le_add_left N j) tendsto_id)
  rw [mul_zero, zero_add] at hlim
  refine ge_of_tendsto' hlim fun N => ?_
  have e : (fun x => L x - fm j x) =
      fun x => (L x - fm (j + N) x) + (fm (j + N) x - fm j x) := by funext x; ring
  rw [e]
  have hA : MemLp (fun x => L x - fm (j + N) x) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) := hL.sub (hmem _)
  have hB : MemLp (fun x => fm (j + N) x - fm j x) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) := (hmem _).sub (hmem _)
  refine (cubeFlat_add_le hA hB).trans ?_
  have h1 := cubeFlat_le_of_sub_const hA 0
  have h2 : cubeL2 k (fun x => (L x - fm (j + N) x) - 0) =
      cubeL2 k (fun x => fm (j + N) x - L x) := by
    rw [← eb6b_cubeL2_neg]
    congr 1; funext x; ring
  rw [h2] at h1
  exact add_le_add h1 (hpart N)

/-- The truncated, mean-free profile of `V (n + j) (ε j)`: it vanishes outside `□_{n+j}` and has
mean zero on `□_n`. -/
noncomputable def eb6b_F (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (n : ℕ) (ε : ℕ → Vec d) (j : ℕ) :
    Vec d → ℝ :=
  (engCube d (n + j)).indicator fun x => V (n + j) (ε j) x -
    ∫ y, V (n + j) (ε j) y ∂(normalizedCubeMeasure (originCube d (n : ℤ)))

theorem eb6b_F_apply {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {n : ℕ} {ε : ℕ → Vec d} {j : ℕ}
    {x : Vec d} (hx : x ∈ engCube d (n + j)) :
    eb6b_F V n ε j x = V (n + j) (ε j) x -
      ∫ y, V (n + j) (ε j) y ∂(normalizedCubeMeasure (originCube d (n : ℤ))) := by
  unfold eb6b_F
  rw [Set.indicator_of_mem hx]

theorem eb6b_F_memLp {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {n : ℕ} {ε : ℕ → Vec d} {j : ℕ}
    (h : MemLp (V (n + j) (ε j)) 2 (normalizedCubeMeasure (originCube d ((n + j : ℕ) : ℤ))))
    (k : ℕ) : MemLp (eb6b_F V n ε j) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
  eb6b_memLp_trunc (h.sub (memLp_const _)) k

theorem eb6b_F_mean {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {n : ℕ} {ε : ℕ → Vec d} {j : ℕ}
    (h : MemLp (V (n + j) (ε j)) 2 (normalizedCubeMeasure (originCube d ((n + j : ℕ) : ℤ)))) :
    ∫ x, eb6b_F V n ε j x ∂(normalizedCubeMeasure (originCube d (n : ℤ))) = 0 := by
  have hp := e0b_isProb (d := d) n
  have hae : eb6b_F V n ε j =ᵐ[normalizedCubeMeasure (originCube d (n : ℤ))]
      fun x => V (n + j) (ε j) x -
        ∫ y, V (n + j) (ε j) y ∂(normalizedCubeMeasure (originCube d (n : ℤ))) :=
    eb6b_ae_cube (fun x hx => eb6b_F_apply (eb6b_cube_mono (Nat.le_add_right n j) hx))
  rw [integral_congr_ae hae, integral_sub
    ((eb6b_memLp_down (Nat.le_add_right n j) h).integrable one_le_two) (integrable_const _)]
  simp

theorem eb6b_F_inc [NeZero d] {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {n : ℕ} {ε : ℕ → Vec d}
    {j k : ℕ} (hk : k ≤ n + j)
    (hV : MemLp (V (n + j) (ε j)) 2 (normalizedCubeMeasure (originCube d ((n + j : ℕ) : ℤ))))
    (hV' : MemLp (V (n + (j + 1)) (ε (j + 1))) 2
      (normalizedCubeMeasure (originCube d ((n + (j + 1) : ℕ) : ℤ)))) :
    cubeFlat k (fun x => eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x) =
      cubeFlat k (fun x => V (n + (j + 1)) (ε (j + 1)) x - V (n + j) (ε j) x) := by
  have hk2 : k ≤ n + (j + 1) := by omega
  have h1 : cubeFlat k (fun x => eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x) =
      cubeFlat k (fun x => (V (n + (j + 1)) (ε (j + 1)) x - V (n + j) (ε j) x) +
        ((∫ y, V (n + j) (ε j) y ∂(normalizedCubeMeasure (originCube d (n : ℤ)))) -
          ∫ y, V (n + (j + 1)) (ε (j + 1)) y ∂(normalizedCubeMeasure (originCube d (n : ℤ))))) := by
    refine eb6b_cubeFlat_congr fun x hx => ?_
    have hx1 : x ∈ engCube d (n + j) := eb6b_cube_mono hk hx
    have hx2 : x ∈ engCube d (n + (j + 1)) := eb6b_cube_mono hk2 hx
    rw [eb6b_F_apply hx1, eb6b_F_apply hx2]
    ring
  rw [h1]
  exact cubeFlat_add_const ((eb6b_memLp_down hk2 hV').sub (eb6b_memLp_down hk hV)) _

theorem eb6b_limit_prep [NeZero d] (Cin Cz : ℝ) {η κ : ℝ} (hη : 1 / 2 ≤ η) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1 / 24) {a : CoeffField d} {δ s : ℕ → ℝ} {mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hCz : 1 ≤ Cz)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ Cz * δ j ≤ κ)
    (hanti : ∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hHC : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d k) u g →
        cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u)
    (hcons : ∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
      affSlope n (V (m + 1) e') = affSlope n (V m e) →
      engNorm (e' - e) ≤ Cz * δ m * engNorm e ∧
        ∀ k : ℕ, n ≤ k → k ≤ m →
          cubeFlat k (fun x => V (m + 1) e' x - V m e x) ≤
            Cz * δ m * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    {n : ℕ} (hn : mstar ≤ n) (ε : ℕ → Vec d)
    (hε : ∀ j : ℕ, affSlope n (V (n + j + 1) (ε (j + 1))) = affSlope n (V (n + j) (ε j))) :
    ∃ gm : ℕ → Vec d → Vec d,
      (∀ m k : ℕ, MemLp (eb6b_F V n ε m) 2
        (normalizedCubeMeasure (originCube d (k : ℤ)))) ∧
      (∀ (m k : ℕ) (i : Fin d),
        MemLp (fun x => gm m x i) 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) ∧
      (∀ m K : ℕ, K ≤ m → IsSolOn a (engCube d K) (eb6b_F V n ε m) (gm m)) ∧
      (∀ k : ℕ, Summable fun m => cubeL2 k (fun x => eb6b_F V n ε (m + 1) x -
        eb6b_F V n ε m x)) ∧
      (∀ (k : ℕ) (i : Fin d), Summable fun m => cubeL2 k (fun x => gm (m + 1) x i - gm m x i)) := by
  have hnj : ∀ j : ℕ, mstar ≤ n + j := fun j => hn.trans (Nat.le_add_right n j)
  choose G hG using fun j : ℕ => hVsol (n + j) (hnj j) (ε j)
  have hVm : ∀ j : ℕ, MemLp (V (n + j) (ε j)) 2
      (normalizedCubeMeasure (originCube d ((n + j : ℕ) : ℤ))) := fun j => (hG j).memLp.1
  have hc := fun j : ℕ => hcons n (n + j) hn (Nat.le_add_right n j) (ε j) (ε (j + 1)) (hε j)
  have hD : ∀ i j : ℕ, i ≤ j → δ (n + j) ≤ δ (n + i) := fun i j hij =>
    hanti (n + i) (n + j) (hnj i) (by omega)
  have hD0 : ∀ i : ℕ, 0 ≤ δ (n + i) := fun i => (hδ (n + i) (hnj i)).1
  have hN : ∀ j i : ℕ, engNorm (ε (j + i)) ≤ (3 : ℝ) ^ (κ * (i : ℝ)) * engNorm (ε j) :=
    eb6b_growth hκ.le (B := fun j => Cz * δ (n + j)) (fun j => (hc j).1)
      (fun j => (hδ (n + j) (hnj j)).2)
  obtain ⟨gm, hgm⟩ : ∃ gm : ℕ → Vec d → Vec d,
      ∀ j, gm j = (engCube d (n + j)).indicator (G j) := ⟨_, fun _ => rfl⟩
  have hgm_apply : ∀ j x i, x ∈ engCube d (n + j) → gm j x i = G j x i := fun j x i hx => by
    rw [hgm, Set.indicator_of_mem hx]
  have hgm_comp : ∀ (j : ℕ) (i : Fin d), (fun x => gm j x i) =
      (engCube d (n + j)).indicator (fun x => G j x i) := fun j i => by
    funext x
    by_cases hx : x ∈ engCube d (n + j)
    · rw [hgm_apply j x i hx, Set.indicator_of_mem hx]
    · rw [hgm, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      rfl
  have hmem : ∀ m k : ℕ, MemLp (eb6b_F V n ε m) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) := fun m k => eb6b_F_memLp (hVm m) k
  have hgmem : ∀ (m k : ℕ) (i : Fin d),
      MemLp (fun x => gm m x i) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    fun m k i => by
      rw [hgm_comp]
      exact eb6b_memLp_trunc (eb6b_grad_comp_memLp (hG m) i) k
  have hsol : ∀ m K : ℕ, K ≤ m → IsSolOn a (engCube d K) (eb6b_F V n ε m) (gm m) := by
    intro m K hK
    have h1 := IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
      (eb6b_cube_mono (hK.trans (Nat.le_add_left m n))) (volume_openCubeSet_lt_top _).ne
      (hell K) (hG m)
    have h2 := IsSolOn.add_const (volume_openCubeSet_lt_top _).ne
      (-∫ y, V (n + m) (ε m) y ∂(normalizedCubeMeasure (originCube d (n : ℤ)))) h1
    refine eb6b_solOn_congr (measurableSet_openCubeSet _) h2 (fun x hx => ?_) (fun x hx => ?_)
    · rw [eb6b_F_apply (eb6b_cube_mono (hK.trans (Nat.le_add_left m n)) hx)]
      ring
    · funext i
      exact (hgm_apply m x i (eb6b_cube_mono (hK.trans (Nat.le_add_left m n)) hx)).symm
  refine ⟨gm, hmem, hgmem, hsol, ?_, ?_⟩
  · intro k
    have hkJ : k ≤ max k n := le_max_left _ _
    have hnJ : n ≤ max k n := le_max_right _ _
    generalize max k n = J at hkJ hnJ
    refine eb6b_summable_of_bound (η := η) (κ := κ) (n := n) (k := J)
      (C := (3 : ℝ) ^ (d * J) * ((1 + (3 : ℝ) ^ (d * J)) * (3 : ℝ) ^ J) * Cz) hη hκ1
      (mul_nonneg (by positivity) (by linarith only [hCz])) (D := fun j => δ (n + j))
      (N := fun j => engNorm (ε j)) hD hD0 hN (fun j => engNorm_nonneg _)
      (fun j => cubeL2_nonneg _ _) J ?_
    intro j hj
    have hJj : J ≤ n + j := hj.trans (Nat.le_add_left j n)
    have hd1 : MemLp (fun x => eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x) 2
        (normalizedCubeMeasure (originCube d (J : ℤ))) := (hmem _ J).sub (hmem _ J)
    have hmean : ∫ x, (eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x)
        ∂(normalizedCubeMeasure (originCube d (n : ℤ))) = 0 := by
      rw [integral_sub ((hmem (j + 1) n).integrable one_le_two)
        ((hmem j n).integrable one_le_two), eb6b_F_mean (hVm (j + 1)), eb6b_F_mean (hVm j)]
      simp
    have h1 := eb6b_cubeL2_le_scale hkJ hd1
    have h2 := eb6b_cubeL2_le_flat hnJ hd1 hmean
    have h5 := (eb6b_F_inc hJj (hVm j) (hVm (j + 1))).trans_le ((hc j).2 J hnJ hJj)
    have h6 : (3 : ℝ) ^ J * cubeFlat J (fun x => eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x) ≤
        (3 : ℝ) ^ J * (Cz * δ (n + j) * (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (J : ℝ)))) *
          engNorm (ε j)) := mul_le_mul_of_nonneg_left h5 (by positivity)
    have h7 : (1 + (3 : ℝ) ^ (d * J)) * ((3 : ℝ) ^ J *
          cubeFlat J (fun x => eb6b_F V n ε (j + 1) x - eb6b_F V n ε j x)) ≤
        (1 + (3 : ℝ) ^ (d * J)) * ((3 : ℝ) ^ J * (Cz * δ (n + j) *
          (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (J : ℝ)))) * engNorm (ε j))) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 := mul_le_mul_of_nonneg_left (h2.trans h7) (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (d * J))
    refine (h1.trans h8).trans (le_of_eq ?_)
    ring
  · intro k i
    have hkJ : k ≤ max k n := le_max_left _ _
    have hnJ : n ≤ max k n := le_max_right _ _
    generalize max k n = J at hkJ hnJ
    refine eb6b_summable_of_bound (η := η) (κ := κ) (n := n) (k := J + 2)
      (C := (3 : ℝ) ^ (d * J) * (|Cin| * Real.sqrt (s (J + 2))) * Cz) hη hκ1
      (mul_nonneg (by positivity) (by linarith only [hCz])) (D := fun j => δ (n + j))
      (N := fun j => engNorm (ε j)) hD hD0 hN (fun j => engNorm_nonneg _)
      (fun j => cubeL2_nonneg _ _) (J + 2) ?_
    intro j hj
    have hJj : J + 2 ≤ n + j := hj.trans (Nat.le_add_left j n)
    have hJ0 : J ≤ n + j := by omega
    have hJ1 : J ≤ n + (j + 1) := by omega
    have hcomp : MemLp (fun x => G (j + 1) x i - G j x i) 2
        (normalizedCubeMeasure (originCube d (J : ℤ))) :=
      (eb6b_memLp_down hJ1 (eb6b_grad_comp_memLp (hG (j + 1)) i)).sub
        (eb6b_memLp_down hJ0 (eb6b_grad_comp_memLp (hG j) i))
    have hsolJ2 : IsSolOn a (engCube d (J + 2))
        (fun x => V (n + (j + 1)) (ε (j + 1)) x - V (n + j) (ε j) x)
        (fun x => G (j + 1) x - G j x) :=
      IsSolOn.sub (hell (J + 2))
        (IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
          (eb6b_cube_mono (by omega)) (volume_openCubeSet_lt_top _).ne (hell _) (hG (j + 1)))
        (IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
          (eb6b_cube_mono (by omega)) (volume_openCubeSet_lt_top _).ne (hell _) (hG j))
    have hnorm : MemLp (fun x => engNorm (G (j + 1) x - G j x)) 2
        (normalizedCubeMeasure (originCube d (J : ℤ))) :=
      eb6b_memLp_down (by omega : J ≤ J + 2) hsolJ2.memLp.2
    have hH := hHC (J + 2) (by omega) _ _ hsolJ2
    rw [Nat.add_sub_cancel] at hH
    have hflat := (hc j).2 (J + 2) (by omega) hJj
    have e1 : cubeL2 J (fun x => gm (j + 1) x i - gm j x i) =
        cubeL2 J (fun x => (fun x => G (j + 1) x - G j x) x i) :=
      eb6b_cubeL2_congr fun x hx => by
        rw [hgm_apply (j + 1) x i (eb6b_cube_mono (by omega) hx),
          hgm_apply j x i (eb6b_cube_mono (by omega) hx)]
        rfl
    have h1 : cubeL2 k (fun x => gm (j + 1) x i - gm j x i) ≤
        (3 : ℝ) ^ (d * J) * cubeL2 J (fun x => gm (j + 1) x i - gm j x i) :=
      eb6b_cubeL2_le_scale hkJ ((hgmem (j + 1) J i).sub (hgmem j J i))
    have h2 := eb6b_cubeL2_comp_le (F := fun x => G (j + 1) x - G j x) i hcomp hnorm
    have hs0 : 0 ≤ |Cin| * Real.sqrt (s (J + 2)) := by positivity
    have h3 : Cin * Real.sqrt (s (J + 2)) * cubeFlat (J + 2)
          (fun x => V (n + (j + 1)) (ε (j + 1)) x - V (n + j) (ε j) x) ≤
        |Cin| * Real.sqrt (s (J + 2)) * (Cz * δ (n + j) *
          (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - ((J + 2 : ℕ) : ℝ)))) * engNorm (ε j)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
        hflat (cubeFlat_nonneg _ _) hs0
    rw [e1] at h1
    have h4 := mul_le_mul_of_nonneg_left (h2.trans (hH.trans h3))
      (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (d * J))
    refine (h1.trans h4).trans (le_of_eq ?_)
    ring

theorem eb6b_limit_one [NeZero d] (Cin Cz : ℝ) {η κ : ℝ} (hη : 1 / 2 ≤ η) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1 / 24) {a : CoeffField d} {δ s : ℕ → ℝ} {mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hCz : 1 ≤ Cz)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ Cz * δ j ≤ κ)
    (hanti : ∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i)
    (hGE : GrowthElliptic a)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hHC : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d k) u g →
        cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u)
    (hcons : ∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
      affSlope n (V (m + 1) e') = affSlope n (V m e) →
      engNorm (e' - e) ≤ Cz * δ m * engNorm e ∧
        ∀ k : ℕ, n ≤ k → k ≤ m →
          cubeFlat k (fun x => V (m + 1) e' x - V m e x) ≤
            Cz * δ m * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    {n : ℕ} (hn : mstar ≤ n) (ε : ℕ → Vec d)
    (hε : ∀ j : ℕ, affSlope n (V (n + j + 1) (ε (j + 1))) = affSlope n (V (n + j) (ε j))) :
    ∃ (L : Vec d → ℝ) (Glim : Vec d → Vec d),
      (∀ᵐ x ∂volume, Tendsto (fun j => eb6b_F V n ε j x) atTop (𝓝 (L x))) ∧
      IsEntireSolution a L Glim ∧
      ∀ j k : ℕ, n ≤ k → k ≤ n + j →
        cubeFlat k (fun x => L x - V (n + j) (ε j) x) ≤
          Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ * δ (n + j) *
            (3 : ℝ) ^ (-((η - 6 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) * engNorm (ε j) := by
  obtain ⟨gm, hmem, hgmem, hsol, hsum, hgsum⟩ :=
    eb6b_limit_prep Cin Cz hη hκ hκ1 hCz hδ hanti hell hVsol hHC hcons hn ε hε
  obtain ⟨L, Glim, hae, hconv, hent⟩ := eb6b_entire_limit hGE hell hmem hgmem hsol hsum hgsum
  refine ⟨L, Glim, hae, hent, ?_⟩
  intro j k hnk hkj
  have hnj : ∀ j : ℕ, mstar ≤ n + j := fun j => hn.trans (Nat.le_add_right n j)
  have hVm : ∀ j : ℕ, MemLp (V (n + j) (ε j)) 2
      (normalizedCubeMeasure (originCube d ((n + j : ℕ) : ℤ))) := fun j =>
    (hVsol (n + j) (hnj j) (ε j)).elim fun g hg => hg.memLp.1
  have hc := fun j : ℕ => hcons n (n + j) hn (Nat.le_add_right n j) (ε j) (ε (j + 1)) (hε j)
  have hD : ∀ i : ℕ, δ (n + (j + i)) ≤ δ (n + (j + 0)) := fun i =>
    hanti (n + j) (n + (j + i)) (hnj j) (by omega)
  have hD0 : ∀ i : ℕ, 0 ≤ δ (n + (j + i)) := fun i => (hδ _ (hnj _)).1
  have hN : ∀ j : ℕ, ∀ i : ℕ, engNorm (ε (j + i)) ≤ (3 : ℝ) ^ (κ * (i : ℝ)) * engNorm (ε j) :=
    eb6b_growth hκ.le (B := fun j => Cz * δ (n + j)) (fun j => (hc j).1)
      (fun j => (hδ (n + j) (hnj j)).2)
  have hf : ∀ i : ℕ, cubeFlat k (fun x => eb6b_F V n ε (j + i + 1) x - eb6b_F V n ε (j + i) x) ≤
      Cz * δ (n + (j + i)) *
        (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) + (i : ℝ) - (k : ℝ)))) *
          engNorm (ε (j + i)) := by
    intro i
    have hk' : k ≤ n + (j + i) := by omega
    have h1 := eb6b_F_inc hk' (hVm (j + i)) (hVm (j + i + 1))
    have h2 := (hc (j + i)).2 k hnk hk'
    have hcast : (((n + (j + i) : ℕ)) : ℝ) = ((n + j : ℕ) : ℝ) + (i : ℝ) := by
      push_cast; ring
    rw [hcast] at h2
    exact h1.trans_le h2
  have h3 := fun i : ℕ => eb6b_tail_real (η := η) (κ := κ) (Cz := Cz)
    (m0 := ((n + j : ℕ) : ℝ)) (k0 := (k : ℝ)) hη hκ1 (by linarith only [hCz])
    (D := fun i => δ (n + (j + i))) (N := fun i => engNorm (ε (j + i)))
    (f := fun i => cubeFlat k (fun x => eb6b_F V n ε (j + i + 1) x - eb6b_F V n ε (j + i) x))
    hD hD0 (fun i => hN j i) (fun i => engNorm_nonneg _) hf i
  have hb : ∀ i : ℕ, cubeFlat k (fun x => eb6b_F V n ε (j + i + 1) x - eb6b_F V n ε (j + i) x) ≤
      (Cz * δ (n + j) * (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) *
        engNorm (ε j)) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ i := fun i => h3 i
  have ha : Summable fun i : ℕ => (Cz * δ (n + j) *
      (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) * engNorm (ε j)) *
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ i :=
    (summable_geometric_of_lt_one eb6b_geom_pos.le eb6b_geom_lt_one).mul_left _
  have htail := eb6b_flat_tail (hmem · k) (hconv k).1 (hconv k).2 ha j hb
  rw [tsum_mul_left, tsum_geometric_of_lt_one eb6b_geom_pos.le eb6b_geom_lt_one] at htail
  have hshift : cubeFlat k (fun x => L x - V (n + j) (ε j) x) =
      cubeFlat k (fun x => L x - eb6b_F V n ε j x) := by
    have e := eb6b_cubeFlat_congr (k := k) (f := fun x => L x - V (n + j) (ε j) x)
      (g := fun x => (L x - eb6b_F V n ε j x) +
        (-∫ y, V (n + j) (ε j) y ∂(normalizedCubeMeasure (originCube d (n : ℤ)))))
      (fun x hx => by
        rw [eb6b_F_apply (eb6b_cube_mono hkj hx)]
        ring)
    rw [e]
    exact cubeFlat_add_const ((hconv k).1.sub (hmem j k)) _
  rw [hshift]
  refine htail.trans ?_
  have hm : (k : ℝ) ≤ ((n + j : ℕ) : ℝ) := by exact_mod_cast hkj
  have hp : (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) ≤
      (3 : ℝ) ^ (-((η - 6 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith only [hm, hκ]
  have hr : 0 < (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := inv_pos.2 (by linarith only [eb6b_geom_lt_one])
  have hd := hD0 0
  have hnn := engNorm_nonneg (ε j)
  have hCz0 : 0 ≤ Cz := by linarith only [hCz]
  calc Cz * δ (n + j) * (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) *
        engNorm (ε j) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹
      = (Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ * δ (n + j)) *
        (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) * engNorm (ε j) := by ring
    _ ≤ _ := by
      have : 0 ≤ Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ * δ (n + j) := by
        have := hD0 0
        exact mul_nonneg (mul_nonneg hCz0 hr.le) this
      gcongr

end SuperdiffusionCLT.Section6
