import Mathlib.Geometry.Manifold.Diffeomorph

variable {N M 𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [TopologicalSpace H]
variable [TopologicalSpace N] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
variable [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M]


variable {M' : Type*} [TopologicalSpace M']
variable (H) in
/-- Given a homeomorphism `f : M ≃ₜ M'`, endow `M'` with a `ChartedSpace` structure by pushing
forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
def Homeomorph.chartedSpace (f : M ≃ₜ M') : ChartedSpace H M' :=
  f.isLocalHomeomorph.chartedSpace f.surjective

namespace Homeomorph


open IsManifold in lemma chartedSpace_trans_mem_maximalAtlas (φ : M ≃ₜ N) :
    letI := φ.chartedSpace H
    ∀ e ∈ atlas H N, φ.toOpenPartialHomeomorph.trans e ∈ maximalAtlas I n M := fun e he ↦ by
  simp only [atlas, ChartedSpace.atlas, mem_setOf_eq] at he
  rcases he with ⟨q, he⟩
  rw [← he, ← OpenPartialHomeomorph.trans_assoc]
  exact StructureGroupoid.mem_maximalAtlas_of_eqOnSource
    (Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans'
      (φ.toOpenPartialHomeomorph_trans_localInverseAt _)
      (OpenPartialHomeomorph.eqOnSource_refl _)) (by rw [OpenPartialHomeomorph.ofSet_trans]))
    <| restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas _)
      <| by simpa using OpenPartialHomeomorph.open_source _

end Homeomorph
