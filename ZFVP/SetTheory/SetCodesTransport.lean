import ZFVP.SetTheory.SetCodes
import ZFVP.SetTheory.EndExtensionRecursion

/-! Transitive collapses move along membership end extensions.

A membership end extension carries a transitive collapse computed in the smaller model to a
transitive collapse in the larger one. Since a transitive collapse forces its relation to be
internally well founded, the transported collapse is again the Mostowski collapse there, so the
Mostowski map and its values commute with the extension. Together with `exists_set_code` this
identifies a set from its ordinal code across the extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable (j : MembershipEndExtension V W)

/-- The image of a transitive collapse under a membership end extension is a transitive collapse. -/
theorem isTransitiveCollapse_map {R D C f : V} (h : IsTransitiveCollapse R D C f) :
    IsTransitiveCollapse (j R) (j D) (j C) (j f) := by
  obtain ⟨hC, hf, hrange, hinj, hmem⟩ := h
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = D := domain_eq_of_mem_function hf
  refine ⟨?_, (j.function_iff f D C).mpr hf, ?_, ?_, ?_⟩
  · constructor
    intro y hy z hz
    obtain ⟨u, hu, rfl⟩ := j.endExtension C y hy
    obtain ⟨v, hv, rfl⟩ := j.endExtension u z hz
    exact (j.mem_iff _ _).mpr (hC.transitive u hu v hv)
  · rw [← j.map_range f, hrange]
  · intro a ha b hb heq
    obtain ⟨u, hu, rfl⟩ := j.endExtension D a ha
    obtain ⟨v, hv, rfl⟩ := j.endExtension D b hb
    rw [← j.map_value f u (by rw [hdom]; exact hu),
      ← j.map_value f v (by rw [hdom]; exact hv)] at heq
    exact congrArg j (hinj u hu v hv (j.injective heq))
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := j.endExtension D a ha
    obtain ⟨v, hv, rfl⟩ := j.endExtension D b hb
    rw [← j.map_value f u (by rw [hdom]; exact hu),
      ← j.map_value f v (by rw [hdom]; exact hv), j.mem_iff, ← j.map_kpair, j.mem_iff]
    exact hmem u hu v hv

/-- Extensionality on a set transfers to the images under a membership end extension. -/
theorem isExtensionalOn_map {R D : V} (h : IsExtensionalOn R D) :
    IsExtensionalOn (j R) (j D) := by
  intro a ha b hb hpred
  obtain ⟨u, hu, rfl⟩ := j.endExtension D a ha
  obtain ⟨v, hv, rfl⟩ := j.endExtension D b hb
  refine congrArg j (h u hu v hv ?_)
  intro z hz
  have hzz := hpred (j z) ((j.mem_iff _ _).mpr hz)
  rwa [← j.map_kpair, j.mem_iff, ← j.map_kpair, j.mem_iff] at hzz

/-- Internal well-foundedness of the image, obtained from the transported collapse rather than
from the definition, which quantifies over all subsets of the larger model. -/
theorem isInternallyWellFounded_map {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) : IsInternallyWellFounded (j R) (j D) :=
  isInternallyWellFounded_of_collapse (j.isTransitiveCollapse_map
    (mostowskiMap_isTransitiveCollapse hR hext))

/-- The Mostowski collapse commutes with a membership end extension. -/
theorem mostowskiMap_map {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) :
    j (mostowskiMap R D) = mostowskiMap (j R) (j D) := by
  have hc' := j.isTransitiveCollapse_map (mostowskiMap_isTransitiveCollapse hR hext)
  have hwf' : IsInternallyWellFounded (j R) (j D) := isInternallyWellFounded_of_collapse hc'
  rw [mostowskiMap_of_wellFounded hwf']
  exact (transitiveCollapse_unique hwf' hc').1

/-- A code read in the larger model names the image of the set it names in the smaller one. -/
theorem value_mostowskiMap_map {R D t : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) (ht : t ∈ D) :
    j ((mostowskiMap R D) ‘ t) = (mostowskiMap (j R) (j D)) ‘ (j t) := by
  have hc := mostowskiMap_isTransitiveCollapse hR hext
  have hfun : IsFunction (mostowskiMap R D) := IsFunction.of_mem hc.2.1
  have hdom : domain (mostowskiMap R D) = D := domain_eq_of_mem_function hc.2.1
  rw [j.map_value _ t (by rw [hdom]; exact ht), j.mostowskiMap_map hR hext]

end MembershipEndExtension

end ZFVP
