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
public import Physlib.SpaceAndTime.Time.TimeMan
public import Physlib.ClassicalMechanics.Pendulum.ToMathlib
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
  · grind)


noncomputable instance instChartedSpaceConfigurationSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ConfigurationSpace :=
  configurationSpaceHomProd.chartedSpace

--- ConfigurationSpace und Circle × Circle sind diffeomorph
--set_option pp.all true in
noncomputable def diffeo : Diffeomorph ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ConfigurationSpace (Circle × Circle) ω where
  toFun := configurationSpaceHomProd
  invFun := configurationSpaceHomProd.symm
  contMDiff_toFun := by
    rw [ContMDiff]
    intro x
    rw [contMDiffAt_iff]
    constructor
    · simp
      exact map_continuousAt configurationSpaceHomProd x
    simp [Function.comp_assoc, configurationSpaceHomProd.chartedSpace_chartAt_eq]
    simp_rw [ModelProd]
    simp [configurationSpaceHomProd, configurationSpaceEquivProd]
    have h : ((fun p => ((chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₁) p.1, (chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₂) p.2)) ∘
    (fun c : ConfigurationSpace => (c.φ₁, c.φ₂)) ∘
      (fun p => { φ₁ := p.1, φ₂ := p.2 }) ∘ fun p =>
        ((chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₁).symm p.1, (chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₂).symm p.2)) = id := by
      ext v i
      simp [OpenPartialHomeomorph.right_inv (chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₁) ⟨trivial, trivial⟩]
      simp [OpenPartialHomeomorph.right_inv (chartAt (EuclideanSpace ℝ (Fin 1)) x.φ₂) ⟨trivial, trivial⟩]
    rw [h]
    exact contDiffWithinAt_id
  contMDiff_invFun := by sorry

instance : IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ ConfigurationSpace := diffeo.isManifold
  diffeo.toHomeomorph.chartedSpace_atlas_eq

#synth IsManifold 𝓘(ℝ,(EuclideanSpace ℝ (Fin 1))) ⊤ Circle

#synth IsManifold (𝓡 1) ⊤ Circle

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (Circle × Circle)

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ ConfigurationSpace -- Sehr gut

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

/-- Wahrscheinlich nicht die Time derivative of r₂ -/
--def r₂_dot := mfderiv ((𝓡 1).prod (𝓡 1)) (Space.manifoldStructure 2) (r₂ P)

def V₁ : ConfigurationSpace → ℝ := fun C ↦
  P.m₁.val * P.g * (r₁ P C 0)

def T₁ (x : ConfigurationSpace) (v : TangentSpace ((𝓡 1).prod (𝓡 1)) x) : ℝ :=
  1/2 * P.m₁.val * P.l₁.val^2 * (v.1 0 ^ 2)

/-- The kinetic Energy in Euclidean Space -/
def kineticEnergy (m : ℝ) (x : Space 2) (v : TangentSpace (Space.manifoldStructure 2) x) : ℝ :=
  1/2 * m * ((v.1 0)^2 + (v.1 1)^2)


/-- Zeitableitung von einer Funktion zu Space 2 -/
def d_t_1 (q : TimeMan → Space 2) := mfderiv (modelWithCornersSelf ℝ ℝ) (Space.manifoldStructure 2) q


/-- Zeitableitung von einer Funktion zu ConfigurationSpace -/
def d_t_2 (q : TimeMan → ConfigurationSpace) := mfderiv (modelWithCornersSelf ℝ ℝ) ((𝓡 1).prod (𝓡 1)) q

lemma mfderiv_r₁_eq (c : ConfigurationSpace) : ∂ₜ

--    mfderiv ((𝓡 1).prod (𝓡 1)) (Space.manifoldStructure 2) (r₁ P) c = sorry := by


/--
Let q : t -> (q_1, q_2) be a trajectory.
The kinetic Energy of the
-/
lemma T₁_eq_kineticEnergy (q : TimeMan → ConfigurationSpace) (t : TimeMan) :
    T₁ P (q t) (d_t_2 q t t.val) = kineticEnergy P.m₁.val (r₁ P (q t)) (d_t_1 ((r₁ P) ∘ q) t t.val) := by
  rw [T₁, kineticEnergy, d_t_1, d_t_2]
  ring_nf






end
end CoplanarDoublePendulum
end ClassicalMechanics
