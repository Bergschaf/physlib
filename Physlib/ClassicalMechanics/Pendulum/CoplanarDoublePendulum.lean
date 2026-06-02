/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
module

public import Physlib.Meta.Linters.Sorry
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.SpaceAndTime.Space.LengthUnit
public import Physlib.ClassicalMechanics.Mass.MassUnit
public import Mathlib.Analysis.Complex.Circle
public import Physlib.SpaceAndTime.TimeAndSpace.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Module.TransferInstance
/-!
# Coplanar Double Pendulum
### Tag: LnL_1.5.1
## Source:
* Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
* Chapter: 1 The Equations of motion
* Section: 5 The Lagrangian for a system of particles
* Problem: 1 Coplanar Double Pendulum

Description: This problem involves:
a) identifying the appropriate Degrees of Freedom or generalized coordinates
and their relation to cartesian coordinates

b) and using them to write down the Lagrangian for

a coplanar double pendulum made up of two
point masses $m_1$ and $m_2$. Mass $m_1$ is attached to the pivot and $m_2$ is attached
to $m_1$ via strings of length $l_1$ and $l_2$ respectively.

Solution:

The Cartesian coordinates $(x_1, y_1)$ for mass $m_1$ and $(x_2, y_2)$ for mass $m_2$ can be
expressed in terms of the two angles $\phi_1$ and $\phi_2$ made by the strings with the vertical:
$$
\begin{aligned}
x_1 &= l_1\sin\phi_1\\
y_1 &= -l_1\cos\phi_1\\
x_2 &= l_1\sin\phi_1 + l_2\sin\phi_2\\
y_2 &= -l_1\cos\phi_1 - l_2\cos\phi_2
\end{aligned}
$$

b) The Lagrangian is obtained by writing down the kinetic and potential energies
first in terms of cartesian coordinates and their time derivates and then substituting
the coordinates and derivatives with transformations obtained in a) :

$$\mathcal{L} = T_1 + T_2 - V_1 - V_2$$ where $T$ denotes the kinetic energy and $V$
the potential energy
$$
\begin{aligned}
T_1 &= \tfrac{1}{2}m_1(\dot{x}_1^2 + \dot{y}_1^2) = \tfrac{1}{2}m_1 l_1^2\dot{\phi}_1^2\\
V_1 &= m_1 g y_1 = -m_1 g l_1\cos\phi_1\\
T_2 &= \tfrac{1}{2}m_2(\dot{x}_2^2 + \dot{y}_2^2)
    = \tfrac{1}{2}m_2\bigl(l_1^2\dot{\phi}_1^2 + l_2^2\dot{\phi}_2^2
      + 2l_1 l_2\dot{\phi}_1\dot{\phi}_2\cos(\phi_1 - \phi_2)\bigr)\\
V_2 &= m_2 g y_2 = -m_2 g\bigl(l_1\cos\phi_1 + l_2\cos\phi_2\bigr)
\end{aligned}
$$

so that the Lagrangian becomes:
    $$
\mathcal{L} = \tfrac{1}{2}(m_1 + m_2)l_1^2\dot{\phi}_1^2 + \tfrac{1}{2}m_2 l_2^2\dot{\phi}_2^2+
  m_2 l_1 l_2\dot{\phi}_1\dot{\phi}_2\cos(\phi_1 - \phi_2)+
  (m_1 + m_2)g l_1\cos\phi_1 + m_2 g l_2\cos\phi_2
$$
-/

@[expose] public section

-- This is already in mathlib but not in the version imported here

section IsLocalHomeomorph
variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}
variable [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace H] [ChartedSpace H M]
open Set OpenPartialHomeomorph Manifold
open TopologicalSpace Topology
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  {f : X → Y} (s : Set X) (t : Set Y)

namespace IsLocalHomeomorph
variable (hf : IsLocalHomeomorph f) {x : X}
variable (x) in
/-- A chosen local inverse for a local homeomorphism `f` at a point `x`. -/
noncomputable def localInverseAt : OpenPartialHomeomorph Y X := (hf x).choose.symm

/-- The point `x` lies in the target of `localInverseAt x`. -/
@[grind =>, simp] lemma self_mem_localInverseAt_target : x ∈ (hf.localInverseAt x).target :=
  (hf x).choose_spec.1
variable (x) in
/-- The inverse function of `localInverseAt x` coincides with `f`. -/
@[simp] lemma localInverseAt_symm : (hf.localInverseAt x).symm = f :=
  (hf x).choose_spec.2.symm
/-- The point `f x` lies in the source of `localInverseAt x`. -/
@[grind =>, simp] lemma apply_self_mem_localInverseAt_source :
    f x ∈ (hf.localInverseAt x).source := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).map_target hf.self_mem_localInverseAt_target
/-- The function `f` is injective on the target of `localInverseAt x`. -/
lemma injOn_localInverseAt_target : (hf.localInverseAt x).target.InjOn f := by
  rw [Set.EqOn.injOn_iff (f₂ := (hf.localInverseAt x).symm) (fun y _ ↦ by simp)]
  exact (hf.localInverseAt x).symm.injOn
/-- If `y` lies in the source of `localInverseAt x`, then `f (localInverseAt x y) = y`. -/
@[grind .] lemma apply_localInverseAt_of_mem {y : Y} (hx : y ∈ (hf.localInverseAt x).source) :
    f (hf.localInverseAt x y) = y := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).left_inv hx
/-- The function `localInverseAt x` sends `f x` back to `x`. -/
@[simp] lemma localInverseAt_apply_self : hf.localInverseAt x (f x) = x :=
  hf.injOn_localInverseAt_target (by simp) hf.self_mem_localInverseAt_target <|
    hf.apply_localInverseAt_of_mem hf.apply_self_mem_localInverseAt_source

end IsLocalHomeomorph

/-- Given a right inverse for a local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace`
structure by pushing forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
noncomputable def IsLocalHomeomorph.chartedSpaceOfRightInverse
    {f : M → M'} (hf : IsLocalHomeomorph f) {g : M' → M} (hg : Function.RightInverse g f) :
    ChartedSpace H M' where
  atlas := {(hf.localInverseAt (g q)).trans (chartAt H (g q)) | q : M'}
  chartAt q := (hf.localInverseAt (g q)).trans (chartAt H (g q))
  mem_chart_source q := by
    nth_rw 3 [← hg.eq q]
    simp
  chart_mem_atlas := by simp
/-- Given a surjective local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace` structure
by pushing forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
noncomputable def IsLocalHomeomorph.chartedSpace
    {f : M → M'} (hf : IsLocalHomeomorph f) (hf' : Function.Surjective f) :
    ChartedSpace H M' :=
  hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec
end IsLocalHomeomorph

namespace ClassicalMechanics
/-
structure HolonomicLagrangeProblem where
  /-- Dimensions -/
  d : ℕ+
  /-- Number of particles -/
  N : ℕ+
  /-- masses -/
  m : Fin N → ℝ
  /-- Degrees of freedom -/
  S : ℕ+
  /-- Enough constraints -/
  constraints : Fin (N - S) → C((Space (d * N) × Time), ℝ)

  constraintsProp : sorry -- they are independent

  configurationSpace : (sorry : Type)-- Manifold??

  transformations : configurationSpace → Space (d * N)

  transformationsProp : sorry -- the transformations satisfy the constraints and are differentiable

  potential : Space (d * N) → ℝ

  kineticEnergy : Space (d * N) → Space (d * N) → ℝ := sorry -- default value with 1/2 * m i * (v i)^2
-/




structure CoplanarDoublePendulum where
  l₁ : LengthUnit
  l₂ : LengthUnit
  m₁ : MassUnit
  m₂ : MassUnit
  g : NNReal

namespace CoplanarDoublePendulum

open Real
open Manifold
open Set

/-- The configuration space of the coplaner double pendulum. -/
structure ConfigurationSpace where
    φ₁ : Circle
    φ₂ : Circle

def prodToSpace (p : ℝ × ℝ) : Space 2 := ⟨![p.1, p.2]⟩

def configurationSpaceEquivProd : ConfigurationSpace ≃ Circle × Circle where
  toFun c := ⟨c.φ₁, c.φ₂⟩
  invFun p := ⟨p.1, p.2⟩

noncomputable instance : TopologicalSpace ConfigurationSpace :=
  configurationSpaceEquivProd.topologicalSpace

noncomputable def configurationSpaceHomProd : ConfigurationSpace  ≃ₜ Circle × Circle :=
 configurationSpaceEquivProd.toHomeomorph (by
  intro s
  simp [IsOpen, TopologicalSpace.IsOpen]
  constructor
  · intro h
    rcases h with ⟨s', ⟨h1,h2⟩⟩
    have := configurationSpaceEquivProd.surjective.preimage_injective h2
    grind
  · grind
  )

lemma  aux' : Topology.IsOpenEmbedding ⇑configurationSpaceEquivProd:= by sorry

lemma  aux : Topology.IsOpenEmbedding ⇑configurationSpaceEquivProd.symm := by
  refine Topology.IsEmbedding.isOpenEmbedding_of_surjective ?_ ?_
  · refine { toIsInducing := ?_, injective := by exact  Equiv.injective configurationSpaceEquivProd.symm }
    rw [Topology.isInducing_iff]
    ext i
    rw [instTopologicalSpaceConfigurationSpace, Equiv.topologicalSpace, TopologicalSpace.induced]
    simp [IsOpen]
    constructor
    · intro h
      use (configurationSpaceEquivProd.symm '' i)
      simp
      sorry
    · simp
      sorry
  · exact Equiv.surjective configurationSpaceEquivProd.symm

--- benutze  IsLocalHomeomorph.chartedSpace für den ChartedSpace
lemma localHomeo : IsLocalHomeomorph configurationSpaceHomProd.symm :=
  configurationSpaceHomProd.symm.isLocalHomeomorph

noncomputable instance : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ConfigurationSpace :=
  localHomeo.chartedSpace <| Homeomorph.surjective configurationSpaceHomProd.symm

instance : Nonempty ConfigurationSpace := ⟨⟨1, 1⟩⟩

--- ConfigurationSpace und Circle × Circle sind diffeomorph
noncomputable def diffeo : Diffeomorph ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ConfigurationSpace (Circle × Circle) ω where
  toFun := configurationSpaceHomProd
  invFun := configurationSpaceHomProd.symm
  contMDiff_toFun := by
    simp [Equiv.coe_fn_mk, configurationSpaceHomProd, configurationSpaceEquivProd]
    sorry
  contMDiff_invFun := by sorry

--- TODO Manifold M -> Diffeo M N -> Manifold N in die Mathlib refine

-- vlt über isManifold_of_contDiffOn ??

lemma contdiffon :  ∀ (e e' : OpenPartialHomeomorph ConfigurationSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))),
  e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ConfigurationSpace →
    e' ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ConfigurationSpace →
      ContDiffOn ℝ ω (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
        (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1))) := by
  intro e1 e2 h1 h2


instance : IsManifold ((𝓡 1).prod (𝓡 1)) ω ConfigurationSpace := isManifold_of_contDiffOn _ _ _
  contdiffon


#synth IsManifold 𝓘(ℝ,(EuclideanSpace ℝ (Fin 1))) ⊤ Circle

#synth IsManifold (𝓡 1) ⊤ Circle

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (Circle × Circle)



noncomputable section

variable  (P : CoplanarDoublePendulum) (C : ConfigurationSpace)

def ConfigurationSpace.phi_1.toReal := C.1.argEquiv
def ConfigurationSpace.phi_2.toReal := C.2.argEquiv

scoped notation "φ₁" => ConfigurationSpace.phi_1.toReal
scoped notation "φ₂" => ConfigurationSpace.phi_2.toReal


open Time
/--
The cartesian coordinates of mass `m₁`.
-/
def r₁ : ConfigurationSpace → Space 2 := fun C ↦
  ⟨![P.l₁.val * sin (φ₁ C), -P.l₁.val * cos (φ₁ C)]⟩

def r₂ : ConfigurationSpace → Space 2 := fun C ↦
  ⟨r₁ P C + ![P.l₂.val * sin (φ₂ C), - P.l₂.val * cos (φ₂ C)]⟩

def V₁ : ConfigurationSpace → ℝ := fun C ↦
  P.m₁.val * P.g * (r₁ P C 0)

def T₁ (x : ConfigurationSpace) (v : TangentSpace (𝓘(ℝ, (Space 2))) x) : ℝ :=
  1/2 * P.m₁.val * P.l₁.val^2 * (v.val 0 ^ 2)



lemma deriv_aux' (q : Time → ConfigurationSpace) (h : Differentiable ℝ q) {t : Time}:
   ‖∂ₜ (r₁ P ∘ q) t‖^2 = ∑ i : Fin 2, (∂ₜ (fun x ↦ (r₁ P (q x) i)) t)^2 := by

  rw [@EuclideanSpace.real_norm_sq_eq]
  simp
  rw [add_eq_add_iff_eq_and_eq]
  constructor
  · congr 1
    sorry
  · sorry
  sorry

def T₁_eq_euclid (q : Time → ConfigurationSpace) (h : Differentiable ℝ q) :
    (fun t ↦ 1/2 * P.m₁.val * ‖deriv (r₁ P ∘ q) t‖^2) = (T₁ P) ∘ ∂ₜ q := by
  ext t
  simp only [one_div, Time.deriv, Function.comp_apply, T₁]
  rw [fderiv_comp]
  · simp
    rw [EuclideanSpace.real_norm_sq_eq ((fderiv ℝ P.r₁ (q t)) ((fderiv ℝ q t) 1))]


    sorry
  · sorry
  · exact Differentiable.differentiableAt h


end
end CoplanarDoublePendulum
end ClassicalMechanics
