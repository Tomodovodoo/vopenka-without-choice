import ZFVP.ModelTheory.InternalFiniteNamingData

/-! A finite name context has an injective external enumeration of precisely
the upper indices it mentions. The context length is a standard natural. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_finiteUpperIndices {I k : V} (hk : k ∈ (ω : V) ^ I)
    (hki : Injective k) (N : ℕ) :
    ∃ (p : ℕ) (indices : Fin p → V), Function.Injective indices ∧
      (∀ t, indices t ∈ I) ∧
      (∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ t, indices t = i) ∧
      ∀ t, k ‘ (indices t) ∈ (N : V) := by
  classical
  let J := {i : V // i ∈ I ∧ k ‘ i ∈ (N : V)}
  have he : ∀ i : J, ∃ t : Fin N, k ‘ i.val = (t.val : V) :=
    fun i ↦ (mem_natCast_iff _ N).mp i.property.2
  choose slot hslot using he
  have hslotinj : Function.Injective slot := by
    intro i j hij
    apply Subtype.ext
    apply injective_value_eq hk hki i.property.1 j.property.1
    exact (hslot i).trans ((congrArg (fun t : Fin N ↦ (t.val : V)) hij).trans (hslot j).symm)
  let : Finite J := Finite.of_injective slot hslotinj
  let : Fintype J := Fintype.ofFinite J
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun t ↦ (e.symm t).val, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact e.symm.injective (Subtype.ext hst)
  · exact fun t ↦ (e.symm t).property.1
  · intro i hi hin
    exact ⟨e ⟨i, hi, hin⟩, congrArg Subtype.val (e.symm_apply_apply _)⟩
  · exact fun t ↦ (e.symm t).property.2

end ZFVP.Schmerl
