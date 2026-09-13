import ZFVP.SetTheory.SetCodesTransport

/-! Transitive collapses come back down along a membership end extension.

`ZFVP.SetTheory.SetCodesTransport` moves a collapse computed in the smaller model up to the larger
one. Here the same statements are moved the other way: if the image of a relation is extensional,
internally well founded, or collapsed by the image of a function, the same holds in the smaller
model. A collapse of the image pair that lives in the larger model is always the image of one in
the smaller model, so the collapse and the sets it produces are recovered downstairs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable (j : MembershipEndExtension V W)

/-- Extensionality of the images gives extensionality downstairs. -/
theorem isExtensionalOn_of_map {R D : V} (h : IsExtensionalOn (j R) (j D)) :
    IsExtensionalOn R D := by
  intro x hx y hy hpred
  refine j.injective (h (j x) ((j.mem_iff _ _).mpr hx) (j y) ((j.mem_iff _ _).mpr hy) ?_)
  intro w hw
  obtain ⟨z, hz, rfl⟩ := j.endExtension D w hw
  rw [← j.map_kpair, j.mem_iff, ← j.map_kpair, j.mem_iff]
  exact hpred z hz

/-- Internal well-foundedness of the images gives internal well-foundedness downstairs. -/
theorem isInternallyWellFounded_of_map {R D : V} (h : IsInternallyWellFounded (j R) (j D)) :
    IsInternallyWellFounded R D := by
  intro A hAD hA
  obtain ⟨a₀, ha₀⟩ := hA.nonempty
  obtain ⟨m, hmA, hmin⟩ := h (j A) ((j.subset_iff A D).mpr hAD)
    ⟨j a₀, (j.mem_iff _ _).mpr ha₀⟩
  obtain ⟨a, ha, rfl⟩ := j.endExtension A m hmA
  refine ⟨a, ha, ?_⟩
  intro b hb hbR
  refine hmin (j b) ((j.mem_iff _ _).mpr hb) ?_
  rw [← j.map_kpair, j.mem_iff]
  exact hbR

/-- A collapse of the images is the image of a collapse in the smaller model. -/
theorem isTransitiveCollapse_of_map {R D C f : V}
    (h : IsTransitiveCollapse (j R) (j D) (j C) (j f)) : IsTransitiveCollapse R D C f := by
  obtain ⟨hC, hf, hrange, hinj, hmem⟩ := h
  have hf' : f ∈ C ^ D := (j.function_iff f D C).mp hf
  have hfun : IsFunction f := IsFunction.of_mem hf'
  have hdom : domain f = D := domain_eq_of_mem_function hf'
  refine ⟨?_, hf', ?_, ?_, ?_⟩
  · constructor
    intro y hy z hz
    exact (j.mem_iff _ _).mp
      (hC.transitive (j y) ((j.mem_iff _ _).mpr hy) (j z) ((j.mem_iff _ _).mpr hz))
  · exact j.injective (by rw [j.map_range f, hrange])
  · intro a ha b hb heq
    refine j.injective (hinj (j a) ((j.mem_iff _ _).mpr ha) (j b) ((j.mem_iff _ _).mpr hb) ?_)
    rw [← j.map_value f a (by rw [hdom]; exact ha), ← j.map_value f b (by rw [hdom]; exact hb),
      heq]
  · intro a ha b hb
    have := hmem (j a) ((j.mem_iff _ _).mpr ha) (j b) ((j.mem_iff _ _).mpr hb)
    rw [← j.map_value f a (by rw [hdom]; exact ha), ← j.map_value f b (by rw [hdom]; exact hb),
      j.mem_iff, ← j.map_kpair, j.mem_iff] at this
    exact this

/-- A collapse of the images, computed anywhere in the larger model, is the image of the collapse
computed in the smaller model. -/
theorem exists_transitiveCollapse_descend {R D : V} {C f : W}
    (h : IsTransitiveCollapse (j R) (j D) C f) :
    ∃ C₀ f₀ : V, C = j C₀ ∧ f = j f₀ ∧ IsTransitiveCollapse R D C₀ f₀ := by
  have hwf' : IsInternallyWellFounded (j R) (j D) := isInternallyWellFounded_of_collapse h
  have hext' : IsExtensionalOn (j R) (j D) := isExtensionalOn_of_collapse h
  have hwf : IsInternallyWellFounded R D := j.isInternallyWellFounded_of_map hwf'
  have hext : IsExtensionalOn R D := j.isExtensionalOn_of_map hext'
  have hc := mostowskiMap_isTransitiveCollapse hwf hext
  have hc' := j.isTransitiveCollapse_map hc
  obtain ⟨hf1, hC1⟩ := transitiveCollapse_unique hwf' h
  obtain ⟨hf2, hC2⟩ := transitiveCollapse_unique hwf' hc'
  exact ⟨range (mostowskiMap R D), mostowskiMap R D, hC1.trans hC2.symm, hf1.trans hf2.symm, hc⟩

/-- The value of the Mostowski collapse of the images at an image point is the image of the value
computed in the smaller model, with the side conditions checked upstairs. -/
theorem value_mostowskiMap_descend {R D : V} {t : V}
    (hwf : IsInternallyWellFounded (j R) (j D)) (hext : IsExtensionalOn (j R) (j D)) (ht : t ∈ D) :
    (mostowskiMap (j R) (j D)) ‘ (j t) = j ((mostowskiMap R D) ‘ t) :=
  (j.value_mostowskiMap_map (j.isInternallyWellFounded_of_map hwf)
    (j.isExtensionalOn_of_map hext) ht).symm

end MembershipEndExtension

end ZFVP
