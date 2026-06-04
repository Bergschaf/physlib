module
public import Mathlib.Geometry.Manifold.Diffeomorph


open Diffeomorph Set Function Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {G : Type*} [TopologicalSpace G] {G' : Type*}
  [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*} [TopologicalSpace N']
  [ChartedSpace G' N'] {n : WithTop ℕ∞} [IsManifold I n M]

/-- Given a homeomorphism `f : M' ≃ₜ M`, endow `M'` with a `ChartedSpace` structure by pulling back
the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
public def Homeomorph.chartedSpace {f : M' ≃ₜ M} : ChartedSpace H M' where
  atlas := {(f.transOpenPartialHomeomorph (chartAt H (f q))) | q : M'}
  chartAt q := (f.transOpenPartialHomeomorph (chartAt H (f q)))
  mem_chart_source q := by simp
  chart_mem_atlas := by simp

public lemma Homeomorph.chartedSpace_chartAt_eq  {f : M' ≃ₜ M} (x : M') :
  @chartAt H _ _ _ f.chartedSpace x = f.transOpenPartialHomeomorph (chartAt H (f x)) := by rfl

public lemma Homeomorph.chartedSpace_atlas_eq {f : M' ≃ₜ M} :
  @atlas H _ _ _ f.chartedSpace = {(f.transOpenPartialHomeomorph (chartAt H (f q))) | q : M'} := by rfl

variable [ChartedSpace H M']
/-- Given a diffeomorphism `f : M' ≃ₘ^n⟮I, I'⟯ M` and given that the `atlas` on `M'` is induced by
`f` (the corresponding `ChartedSpace` instance is defined at `Homeomorph.chartedSpace`), prove that
`M'` is a Manifold with respect to `I`.
-/
@[implicit_reducible]
public def Diffeomorph.isManifold (f : Diffeomorph I I M' M n)
    (h : atlas H M' = {(f.toHomeomorph.transOpenPartialHomeomorph (chartAt H (f q))) | q : M'})
    : IsManifold I n M' where
  compatible := by
    intro e e' he he'
    rw [h] at he he'
    have test := he.out.choose_spec
    obtain ⟨w, h_2⟩ := he
    obtain ⟨w_3, h_3⟩ := he'.out
    subst h_2 h_3
    have h1 : f.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        f.toHomeomorph.toOpenPartialHomeomorph = OpenPartialHomeomorph.ofSet univ (by simp) := by
      ext i <;> simp
    simpa [Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm f.toHomeomorph.toOpenPartialHomeomorph
          (chartAt H (f w)),
      ← OpenPartialHomeomorph.trans_assoc _ _ (chartAt _ _), OpenPartialHomeomorph.trans_assoc, h1,
      OpenPartialHomeomorph.ofSet_univ_eq_refl, OpenPartialHomeomorph.trans_refl]
    using StructureGroupoid.compatible (contDiffGroupoid n I)
                  (chart_mem_atlas _ _) (chart_mem_atlas _ _)
