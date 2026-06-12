/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real
public import Physlib.SpaceAndTime.Space.ToMathlib
/-!

# Space

In this module, we define the the type `Space d` which corresponds
to `d`-dimensional flat Euclidean space and prove some properties about it.

The scope of this module is to define on `Space d` basic instances related translations and
the metric. We do not here define the structure of a `Module` on `Space d`, as this is done in
`Physlib.SpaceAndTime.Space.Module`.

Physlib sits downstream of Mathlib, and above we import the necessary Mathlib modules
which contain (perhaps transitively through imports) the definitions and theorems we need.

## Implementation details

The exact implementation of `Space d` into Physlib is discussed in numerous places
on the Lean Zulip, including:

- https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/Space.20vs.20EuclideanSpace/with/575332888

There is a choice between defining `Space d` as an `abbrev` of `EuclideanSpace ℝ (Fin d)`,
as a `def` of a type with value `EuclideanSpace ℝ (Fin d)` or as a structure
with a field `val : Fin d → ℝ` :

+---------------------------------------------------+---------+-------+-----------+
|                                                   | abbrev  |  def  | structure |
+---------------------------------------------------+---------+-------+-----------+
| allows casting from `EuclideanSpace`              |   yes   |  yes  |    no     |
| carries instances from `EuclideanSpace`           |   yes   |  no   |    no     |
| requires reproving of lemmas from `EuclideanSpace`|   no    |  yes  |    yes    |
+---------------------------------------------------+---------+-------+-----------+

The `structure` is the most conservative choice, as everything needs redefining. However,
there is are two benefits of using it:

1. It allows us to be precise about the instances we define on `Space d`, and makes
  future refactoring of those instances easier.
2. It allows us to give the necessary physics context to results about `Space d`, which
  would not otherwise be possible if we reuse results from Mathlib.

In this module we give `Space d` the instances of a `NormedAddTorsor`
and a `MetricSpace`. These physically correspond to the statement that
you can add a vector to a point in space, and that there is a notion of distance between
points in space. This notion of distance corresponds to a choice of length unit.

In `Physlib.SpaceAndTime.Space.Module` we give `Space d` the structure of a `Module`
(aka vector space), a `Norm` and an `InnerProductSpace`. These require certain choices, for example
the choice of a zero in `Space d`.

This module structure is necessary in numerous places. For example,
the normal derivatives used by physicists `∂_x, ∂_y, ∂_z` require a
module structure.

Because of this, one should be careful to avoid using the explicit zero in `Space d`,
or adding two `Space d` values together. Where possible one should use
the `VAdd (EuclideanSpace ℝ (Fin d)) (Space d)` instance instead.

-/

@[expose] public section

/-!

## A. The `Space` type

-/

/-- The type `Space d` is the world-volume which corresponds to
`d` dimensional (flat) Euclidean space with a given (but arbitrary)
choice of length unit, and a given (but arbitrary) choice of zero.

The default value of `d` is `3`. Thus `Space = Space 3`-/
structure Space (d : ℕ := 3) where
  /-- The underlying map `Fin d → ℝ` associated with a point in `Space`. -/
  val : Fin d → ℝ

namespace Space

lemma eq_of_val {d} {p q : Space d} (h : p.val = q.val) :
    p = q := by
  cases p
  cases q
  congr

@[simp]
lemma val_eq_iff {d} {p q : Space d} :
    p.val = q.val ↔ p = q := by
  apply Iff.intro
  · exact eq_of_val
  · intro h
    rw [h]

/-!

## B. Instances on `Space`

-/

/-!

## B.1. Instance of coercion to functions

-/

instance {d} : CoeFun (Space d) (fun _ => Fin d → ℝ) where
  coe p := p.val

@[ext]
lemma eq_of_apply {d} {p q : Space d}
    (h : ∀ i : Fin d, p i = q i) : p = q := by
  apply eq_of_val
  funext i
  exact h i

/-!

## B.2. The Non-emptiness

-/

instance {d} : Nonempty (Space d) := Nonempty.intro
  ⟨fun _ => Classical.choice instNonemptyOfInhabited⟩

instance : Subsingleton (Space 0) := Subsingleton.intro <| fun _ _ =>
  eq_of_apply <| fun i => Fin.elim0 i

/-!

## B.3.1. The additive action

-/

noncomputable instance : VAdd (EuclideanSpace ℝ (Fin d)) (Space d) where
  vadd v s := ⟨fun i => v i + s.val i⟩

@[simp]
lemma vadd_val {d} (v : EuclideanSpace ℝ (Fin d)) (s : Space d) :
    (v +ᵥ s).val = fun i => v i + s.val i := rfl

@[simp]
lemma vadd_apply {d} (v : EuclideanSpace ℝ (Fin d))
    (s : Space d) (i : Fin d) :
    (v +ᵥ s) i = v i + s i := by rfl

lemma vadd_transitive {d} (s1 s2 : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), v +ᵥ s1 = s2 := by
  use WithLp.toLp 2 fun i => s2 i - s1 i
  ext i
  simp

noncomputable instance : AddAction (EuclideanSpace ℝ (Fin d)) (Space d) where
  zero_vadd s := by
    ext i
    simp
  add_vadd v1 v2 s := by
    ext i
    simp only [vadd_apply, PiLp.add_apply]
    ring

/-!

## B.3.2. Subtraction

-/

noncomputable instance {d} : VSub (EuclideanSpace ℝ (Fin d)) (Space d) where
  vsub s1 s2 := WithLp.toLp 2 <| fun i => s1 i - s2 i

@[simp]
lemma vsub_apply {d} (s1 s2 : Space d) (i : Fin d) :
    (s1 -ᵥ s2) i = s1 i - s2 i := rfl

/-!

## B.3.3. AddTorsor instance

-/

noncomputable instance {d} : AddTorsor (EuclideanSpace ℝ (Fin d)) (Space d) where
  vsub_vadd' s1 s2 := by
    ext i
    simp
  vadd_vsub' s1 s2 := by
    ext i
    simp

/-!

## B.4. PseudoMetricSpace

-/

noncomputable instance {d} : Dist (Space d) where
  dist p q := √ (∑ i, (p i - q i) ^ 2)

lemma dist_eq {d} (p q : Space d) : dist p q = √ (∑ i, (p i - q i) ^ 2) := rfl

noncomputable instance {d} : PseudoMetricSpace (Space d) where
  dist_self x := by simp [dist_eq]
  dist_comm x y := by grind [dist_eq]
  dist_triangle x y z := by
    convert dist_triangle (WithLp.toLp 2 fun i => x i) (WithLp.toLp 2 fun i => y i)
      (WithLp.toLp 2 fun i => z i)
    all_goals
      rw [EuclideanSpace.dist_eq]
      simp only [dist, sq_abs]

/-!

## B.5. NormAddTorsor instance

-/

noncomputable instance {d} : NormedAddTorsor (EuclideanSpace ℝ (Fin d)) (Space d) where
  dist_eq_norm' p q := by simp [dist, EuclideanSpace.norm_eq]

/-!

## B.6. Metric space instance

-/

noncomputable instance {d} : MetricSpace (Space d) where
  eq_of_dist_eq_zero {p q} := by simp [NormedAddTorsor.dist_eq_norm']

/-!

## B.7. Non-trivality

-/

instance {d : ℕ} : Nontrivial (Space d.succ) where
  exists_pair_ne := by
    obtain k := Classical.choice Space.instNonempty
    obtain ⟨v1, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin d.succ))
    use k, v1 +ᵥ k
    simpa only [ne_eq, eq_vadd_iff_vsub_eq, vsub_self] using hv.symm

/-!

## C. Model structure (i.e. structure of a manifold)

-/

open Manifold Real

TODO "Fix the manifold structure on `Space d`. In particular, we should not need to
  define `manifoldStructure`. Instead, we should be able to give `Space d` an instance
  of `IsManifold` directly."

noncomputable def homEuclideanSpaceSpace (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ₜ Space d where
  toFun v := ⟨EuclideanSpace.equiv (Fin d) ℝ v⟩
  invFun s := EuclideanSpace.equiv (Fin d) ℝ|>.symm s.val
  continuous_toFun := by
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε
    simp_all [dist, Real.sqrt_eq_rpow]
  continuous_invFun := by
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε
    simp_all [dist, Real.sqrt_eq_rpow]

noncomputable instance (priority := high) (d : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin d)) (Space d) :=
    (homEuclideanSpaceSpace d).chartedSpace (EuclideanSpace ℝ (Fin d))

instance (d : ℕ) :
    IsManifold (𝓡 d) ⊤ (Space d) :=
  (homEuclideanSpaceSpace d).isManifold

/-
open Manifold in
lemma contMDiff_vaddConst (d : ℕ) : ContMDiff
    (manifoldStructure d) (𝓘(ℝ, EuclideanSpace ℝ (Fin d))) ⊤ (manifoldStructure d).toFun := by
  rw [contMDiff_iff]
  refine ⟨(manifoldStructure d).continuous_toFun, fun x y ↦ ?_⟩
  simp only [extChartAt, OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.refl_source, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.refl_coe,
    ModelWithCorners.toPartialEquiv_coe, PartialEquiv.refl_trans,
    ModelWithCorners.toPartialEquiv_coe_symm, manifoldStructure_comp_manifoldStructure_symm,
    CompTriple.comp_eq, ModelWithCorners.target_eq, Set.preimage_univ, Set.inter_univ]
  exact contDiffOn_id-/

end Space
