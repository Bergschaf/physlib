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
variable [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace H] [ChartedSpace H M]
/-- Given a right inverse for a local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace`
structure by pushing forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
def IsLocalHomeomorph.chartedSpaceOfRightInverse
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
def IsLocalHomeomorph.chartedSpace
    {f : M → M'} (hf : IsLocalHomeomorph f) (hf' : Function.Surjective f) :
    ChartedSpace H M' :=
  hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec
end IsLocalHomeomorph

namespace ClassicalMechanics

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

def aux := IsLocalHomeomorph.chartedSpace


def configurationSpaceEquivProd' : ConfigurationSpace ≃L[ℝ] Circle × Circle := by
  sorry


-- use configurationSpaceEquivProd.Homeomorph.IsOpenEmbedding
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


instance : ChartedSpace (Space 2) ConfigurationSpace where
  atlas := {{ toFun c := ⟨![c.φ₁.argEquiv, c.φ₂.argEquiv]⟩
              invFun r := ⟨Circle.exp (r 0), Circle.exp (r 1)⟩
              source := configurationSpaceEquivProd.symm '' (univ \ {⟨-1, by simp [Submonoid.unitSphere]⟩})
                ×ˢ (univ \ {⟨-1, by simp [Submonoid.unitSphere]⟩})
              target := prodToSpace '' (Ioo (-π) π) ×ˢ (Ioo (-π) π)
              map_source' := by
                simp [configurationSpaceEquivProd, Equiv.coe_fn_mk, image_prod, mem_image2,
                  mem_diff, mem_univ, mem_singleton_iff, true_and, prodToSpace,
                  Circle.argEquiv_apply_coe, mem_image, mem_prod, mem_Ioo, Space.mk.injEq,
                  Matrix.vecCons_inj, and_true, Prod.exists, exists_eq_right_right, exists_eq_right,
                  forall_exists_index, and_imp]
                intro c x1 hx1 x2 hx2 h1
                subst h1
                dsimp only
                constructor
                · constructor
                  · exact Complex.neg_pi_lt_arg _
                  · rw [Complex.arg_lt_pi_iff]
                    rw [Circle.ext_iff, Complex.ext_iff] at hx1
                    simp at hx1
                    sorry -- correct
                · constructor
                  · exact Complex.neg_pi_lt_arg _
                  · sorry

              map_target' := by
                simp [prodToSpace, mem_image, mem_prod, mem_Ioo, Prod.exists,
                  configurationSpaceEquivProd, Equiv.coe_fn_mk, image_prod, Fin.isValue, mem_image2,
                  mem_diff, mem_univ, mem_singleton_iff, true_and, ConfigurationSpace.mk.injEq,
                  exists_eq_right_right, forall_exists_index, and_imp]
                intro x r1 r2 h1 h2 h3 h4 h5
                subst h5
                dsimp
                constructor
                · have h6 :  ⟨-1, instChartedSpaceSpaceOfNatNatConfigurationSpace._proof_1⟩ = Circle.exp π := by
                    ext
                    simp
                  rw [h6]
                  rw [Circle.exp_eq_exp]
                  simp
                  intro z
                  by_cases hC : 0 ≤ z
                  · suffices r1 < π + z * 2 * π by grind
                    apply lt_of_lt_of_le h2
                    simp
                    sorry
                  · suffices π + z * 2 * π < r1 by grind
                    sorry
                sorry

              left_inv' := by simp
              right_inv' := by
                simp only [prodToSpace, mem_image, mem_prod, mem_Ioo, Prod.exists, Fin.isValue,
                  Circle.argEquiv_apply_coe, Circle.coe_exp, forall_exists_index, and_imp]
                intro x r1 r2 h1 h2 h3 h4 h1
                subst h1
                ext i
                fin_cases i
                · simp only [Fin.isValue, Complex.arg_exp, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
                  Fin.zero_eta, Matrix.cons_val_zero, toIocMod_eq_iff, Set.mem_Ioc,
                  le_neg_add_iff_add_le, zsmul_eq_mul, left_eq_add, mul_eq_zero, Int.cast_eq_zero,
                  OfNat.ofNat_ne_zero, pi_ne_zero, or_self, or_false, exists_eq, and_true]
                  grind
                · simp only [Fin.isValue, Complex.arg_exp, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
                  Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, toIocMod_eq_iff,
                  Set.mem_Ioc, le_neg_add_iff_add_le, zsmul_eq_mul, left_eq_add, mul_eq_zero,
                  Int.cast_eq_zero, OfNat.ofNat_ne_zero, pi_ne_zero, or_self, or_false, exists_eq,
                  and_true]
                  grind
              open_source := by

                rw [← Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_]
                · apply IsOpen.prod
                  · rw [← isClosed_compl_iff]
                    rw [compl_diff]
                    simp
                  · sorry -- correct
                · apply Homeomorph.isOpenEmbedding




                  sorry


              open_target := by
                sorry
              continuousOn_toFun := by
                simp only [Circle.argEquiv_apply_coe]
                sorry



              continuousOn_invFun := sorry  } }
  chartAt := sorry
  mem_chart_source := sorry
  chart_mem_atlas := sorry

#check IsManifold

instance : IsManifold (𝓘(ℝ, Space 2)) ⊤ ConfigurationSpace where
  compatible := by sorry


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
