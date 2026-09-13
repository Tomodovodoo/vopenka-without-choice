import ZFVP.ModelTheory.ProjectionQuotientClosureForcing
import ZFVP.ModelTheory.LimitSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def splitForcingSystemFormula : SetTheorySemisentence 4 :=
  f“θ P π E.
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ !value.dfn P j,
      !value.dfn (!value.dfn π (!kpair.dfn i j)) p ∈ !value.dfn P i) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ !value.dfn P i,
      !value.dfn (!value.dfn E (!kpair.dfn i j)) p ∈ !value.dfn P j) ∧
    (∀ i ∈ θ, ∀ p ∈ !value.dfn P i, !value.dfn (!value.dfn E (!kpair.dfn i i)) p = p) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k → ∀ p ∈ !value.dfn P k,
      !value.dfn (!value.dfn π (!kpair.dfn i j)) (!value.dfn (!value.dfn π (!kpair.dfn j k)) p) =
        !value.dfn (!value.dfn π (!kpair.dfn i k)) p) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k → ∀ p ∈ !value.dfn P i,
      !value.dfn (!value.dfn E (!kpair.dfn j k)) (!value.dfn (!value.dfn E (!kpair.dfn i j)) p) =
        !value.dfn (!value.dfn E (!kpair.dfn i k)) p) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ !value.dfn P i,
      !value.dfn (!value.dfn π (!kpair.dfn i j)) (!value.dfn (!value.dfn E (!kpair.dfn i j)) p) = p)”

def coherentThreadFormula : SetTheorySemisentence 3 :=
  f“θ π f. ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ →
    !value.dfn (!value.dfn π (!kpair.dfn i j)) (!value.dfn f j) = !value.dfn f i”

def threadSupportFormula : SetTheorySemisentence 4 :=
  f“θ E f k. k ∈ θ ∧ ∀ j ∈ θ, k ⊆ j →
    !value.dfn f j = !value.dfn (!value.dfn E (!kpair.dfn k j)) (!value.dfn f k)”

def forcingInverseLimitFormula : SetTheorySemisentence 5 :=
  f“I θ P π U. ∀ f, f ∈ I ↔ !boundedFunctionFormula f θ U ∧
    (∀ i ∈ θ, !value.dfn f i ∈ !value.dfn P i) ∧ !coherentThreadFormula θ π f”

def forcingDirectLimitFormula : SetTheorySemisentence 6 :=
  f“D θ P π E U. ∀ f, f ∈ D ↔ (!boundedFunctionFormula f θ U ∧
    (∀ i ∈ θ, !value.dfn f i ∈ !value.dfn P i) ∧ !coherentThreadFormula θ π f) ∧
    ∃ k, !threadSupportFormula θ E f k”

def forcingThreadOrderFormula : SetTheorySemisentence 4 :=
  f“S θ R C. ∀ z, z ∈ S ↔ z ∈ !prod.dfn C C ∧ ∀ i ∈ θ,
    !kpair.dfn (!value.dfn (!kpair.π₁.dfn z) i) (!value.dfn (!kpair.π₂.dfn z) i) ∈ !value.dfn R i”

def forcingThreadCoordinateFormula : SetTheorySemisentence 3 :=
  f“ρ D i. ∀ z, z ∈ ρ ↔ ∃ f ∈ D, z = !kpair.dfn f (!value.dfn f i)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance splitForcingSystemFormula_defined : ℒₛₑₜ-relation₄[V] IsSplitForcingSystem via splitForcingSystemFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [splitForcingSystemFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h ↦ ⟨h.projMaps, h.secMaps, h.secId, h.projComp, h.secComp, h.retraction⟩⟩

instance coherentThreadFormula_defined : ℒₛₑₜ-relation₃[V] IsCoherentThread via coherentThreadFormula :=
  ⟨fun v ↦ by simp [coherentThreadFormula, IsCoherentThread]⟩

instance threadSupportFormula_defined : ℒₛₑₜ-relation₄[V] IsThreadSupport via threadSupportFormula :=
  ⟨fun v ↦ by simp [threadSupportFormula, IsThreadSupport]⟩

instance forcingInverseLimitFormula_defined : ℒₛₑₜ-function₄[V] forcingInverseLimit via forcingInverseLimitFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [forcingInverseLimitFormula, mem_forcingInverseLimit_iff, IsCoherentThread]

instance forcingDirectLimitFormula_defined : ℒₛₑₜ-function₅[V] forcingDirectLimit via forcingDirectLimitFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [forcingDirectLimitFormula, mem_forcingDirectLimit_iff, mem_forcingInverseLimit_iff, IsCoherentThread]

instance forcingThreadOrderFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadOrder via forcingThreadOrderFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [forcingThreadOrderFormula, forcingThreadOrder]

instance forcingThreadCoordinateFormula_defined : ℒₛₑₜ-function₂[V] forcingThreadCoordinate via forcingThreadCoordinateFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [forcingThreadCoordinateFormula, forcingThreadCoordinate, mem_definableGraph_iff]

end ZFVP
