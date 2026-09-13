import ZFVP.ModelTheory.CodedBinaryIsomorphism
import ZFVP.ModelTheory.CodedZFModel
import ZFVP.SetTheory.CountableSets

/-! Transport an actual binary structure along any internal injection. Its
new carrier is the actual range of the injection. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryRelabelEdges (E h : V) : V :=
  {p ∈ range h ×ˢ range h ;
    ⟨(converseGraph h) ‘ (kpair.π₁ p), (converseGraph h) ‘ (kpair.π₂ p)⟩ₖ ∈ E}

instance binaryRelabelEdges_definable : ℒₛₑₜ-function₂[V] binaryRelabelEdges := by
  have hh : ℒₛₑₜ-relation₃[V] (fun R E h ↦ ∀ p, p ∈ R ↔ p ∈ range h ×ˢ range h ∧
      ⟨(converseGraph h) ‘ (kpair.π₁ p), (converseGraph h) ‘ (kpair.π₂ p)⟩ₖ ∈ E) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [binaryRelabelEdges, mem_sep_iff]
  rfl

theorem binaryRelabelEdges_subset (E h : V) : binaryRelabelEdges E h ⊆ range h ×ˢ range h :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem function_mem_range_codomain {A B h : V} (hh : h ∈ B ^ A) : h ∈ range h ^ A := by
  let : IsFunction h := IsFunction.of_mem hh
  simpa only [domain_eq_of_mem_function hh] using IsFunction.mem_function h

theorem binaryRelabelEdges_iff {A B E h x y : V} (hh : h ∈ B ^ A) (hhi : Injective h)
    (hx : x ∈ A) (hy : y ∈ A) :
    ⟨h ‘ x, h ‘ y⟩ₖ ∈ binaryRelabelEdges E h ↔ ⟨x, y⟩ₖ ∈ E := by
  simp only [binaryRelabelEdges, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    converseGraph_value_value hh hhi hx, converseGraph_value_value hh hhi hy]
  exact and_iff_right ⟨function_value_mem (function_mem_range_codomain hh) hx,
    function_value_mem (function_mem_range_codomain hh) hy⟩

noncomputable def binaryRelabelStructure (E h : V) : V :=
  binaryRelationStructureCode (range h) (binaryRelabelEdges E h)

instance binaryRelabelStructure_definable : ℒₛₑₜ-function₂[V] binaryRelabelStructure := by
  unfold binaryRelabelStructure
  definability

@[simp] theorem binaryRelabelStructure_domain (E h : V) : structureDomain (binaryRelabelStructure E h) = range h :=
  binaryRelationStructureCode_domain _ _

theorem binaryRelabel_elementary {A B E h : V} (hA : IsNonempty A)
    (hh : h ∈ B ^ A) (hhi : Injective h) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode A E)
      (binaryRelabelStructure E h) h :=
  codedBinaryEmbedding_of_isomorphism hA (function_mem_range_codomain hh) hhi rfl
    (fun _ hx _ hy ↦ binaryRelabelEdges_iff hh hhi hx hy)

theorem binaryRelabel_codedZF {A B E h : V} (hM : IsCodedZFModel (binaryRelationStructureCode A E))
    (hh : h ∈ B ^ A) (hhi : Injective h) : IsCodedZFModel (binaryRelabelStructure E h) := by
  have hA : IsNonempty A := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  exact (binaryRelabel_elementary hA hh hhi).satisfiesCodedOpenTheory_iff.mp hM

theorem binaryRelabel_countable {A B E h : V} (hA : IsInternallyCountable A) (hh : h ∈ B ^ A) :
    IsInternallyCountable (structureDomain (binaryRelabelStructure E h)) := by
  rw [binaryRelabelStructure_domain]
  let : IsFunction h := IsFunction.of_mem hh
  exact internallyCountable_range (internallyCountable_function (by
    simpa only [domain_eq_of_mem_function hh] using hA))

end ZFVP
