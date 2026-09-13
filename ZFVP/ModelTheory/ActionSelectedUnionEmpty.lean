import ZFVP.ModelTheory.SelectedUnionEmpty
import ZFVP.ModelTheory.ProjectionNameTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem localSelectedUnion_action_empty_of_names_countable [Countable V]
    {B R b T U o π E p δ Q t : V}
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hπ : IsForcingSplitProjection B R T U π E) (hp : p ∈ B)
    (h : ∀ ν ∈ twoStepNames Q t, IsForcingName T ν) (f : ForcingName B)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions T U Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions T U Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    forcingLocalCanonicalName T U o δ (E ‘ p)
      (forcingSelectedUnion T U o (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val)) = ∅ := by
  apply localSelectedUnion_empty_of_names_countable hU ho (function_value_mem hπ.maps hp) h
    ⟨nameAction E f.val, nameAction_isName hπ.maps f.property⟩
  intro H hH hpH
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  let A : ForcingContext V := ⟨B, R, b, forcingProjectionGeneric B R π H,
    hR, hb, hπ.projection.generic hR hH⟩
  have hpA : p ∈ A.G := by
    have hh := hπ.projection.image_mem hR hH.1 hpH
    rwa [hπ.right_inverse p hp] at hh
  obtain ⟨α, hα, htail⟩ := hf A.G A.generic hpA
  let e := A.projectionInclusion C hπ rfl
  refine ⟨e α, ?_, ?_⟩
  · rw [A.projectionInclusion_nameAction C hπ rfl f]
    have hm := (e.function_iff (A.ofName f) α (A.check (twoStepConditions T U Q t))).mpr hα
    rwa [A.projectionInclusion_check C hπ rfl] at hm
  · intro i hi c hc hci
    obtain ⟨a, ha, rfl⟩ := e.endExtension α i hi
    rw [A.projectionInclusion_nameAction C hπ rfl f, ← e.map_value_total] at hci
    obtain ⟨d, hd, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hα ha)
    rw [had, A.projectionInclusion_check C hπ rfl] at hci
    have hdc : d = c := (C.check_eq_iff _ _).mp hci
    exact hdc ▸ htail a ha d hd had

theorem localSelectedUnion_action_empty_countable [Countable V]
    {B R b T U o π E p δ Q S t : V}
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hπ : IsForcingSplitProjection B R T U π E) (hp : p ∈ B)
    (h : IsForcingIterand T U Q S t) (f : ForcingName B)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions T U Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions T U Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    forcingLocalCanonicalName T U o δ (E ‘ p)
      (forcingSelectedUnion T U o (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val)) = ∅ :=
  localSelectedUnion_action_empty_of_names_countable hR hb hU ho hπ hp (fun _ hν ↦ h.name hν) f hf

end ZFVP
