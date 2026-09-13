import ZFVP.ModelTheory.ForcingIterationColumns
import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingCodeUniverse (s : V) : V := ⋃ˢ range (forcingCodeP s)

theorem IsForcingIterationCode.subset_universe {θ s : V}
    (h : IsForcingIterationCode θ s) : ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ forcingCodeUniverse s := by
  intro i hi x hx
  have hf : IsFunction (forcingCodeP s) := h.tableP.function
  have hi' : i ∈ domain (forcingCodeP s) := h.tableP.domain_eq.symm ▸ hi
  apply mem_sUnion_iff.mpr
  exact ⟨(forcingCodeP s) ‘ i, mem_range_iff.mpr
    ⟨i, kpair_value_mem hi'⟩, hx⟩

noncomputable def forcingThreadCode (θ s C : V) : V :=
  forcingIterationCodeNext θ s C (forcingThreadOrder θ (forcingCodeR s) C)
    (forcingLimitProjectionColumn θ C)
    (forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s))
    (forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s))
    (forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) ∅ ((forcingCodet s) ‘ ∅))

noncomputable def forcingDirectCode (θ s : V) : V :=
  forcingThreadCode θ s (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s)
    (forcingCodeE s) (forcingCodeUniverse s))

noncomputable def forcingInverseCode (θ s : V) : V :=
  forcingThreadCode θ s (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s)
    (forcingCodeUniverse s))

theorem forcingDirectCode_valid {θ s : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) :
    IsForcingIterationCode (succ θ) (forcingDirectCode θ s) :=
  h.extend (h.system.directColumn h0 h.subset_universe)

theorem forcingInverseCode_valid {θ s : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) :
    IsForcingIterationCode (succ θ) (forcingInverseCode θ s) :=
  h.extend (h.system.inverseColumn h0 h.subset_universe)

theorem forcingThreadCode_extends {θ s : V} (h : IsForcingIterationCode θ s) (C : V) :
    ForcingCodeExtends s (forcingThreadCode θ s C) := h.extends_next _ _ _ _ _ _

@[simp] theorem forcingThreadCode_poset (θ s C : V) :
    (forcingCodeP (forcingThreadCode θ s C)) ‘ θ = C := by
  simp [forcingThreadCode, forcingIterationCodeNext, forcingFamilyNext_new]

@[simp] theorem forcingThreadCode_order (θ s C : V) :
    (forcingCodeR (forcingThreadCode θ s C)) ‘ θ = forcingThreadOrder θ (forcingCodeR s) C := by
  simp [forcingThreadCode, forcingIterationCodeNext, forcingFamilyNext_new]

@[simp] theorem forcingThreadCode_top (θ s C : V) :
    (forcingCodet (forcingThreadCode θ s C)) ‘ θ =
      forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) ∅ ((forcingCodet s) ‘ ∅) := by
  simp [forcingThreadCode, forcingIterationCodeNext, forcingFamilyNext_new]

end ZFVP
