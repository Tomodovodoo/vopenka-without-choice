import ZFVP.ModelTheory.InternalElementaryDiagram
import ZFVP.ModelTheory.InternalBinaryQuotientTruth
import ZFVP.SetTheory.InjectionRetraction

/-! Elementary-diagram requirements with fixed internal names. The requirements
form an actual countable set, are jointly realized in the source by an internal
retraction, and yield an elementary embedding when a name truth table realizes
them and is passed to its equality quotient. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedElementaryDiagram (L M j : V) : V :=
  repl (fun p ↦ ⟨kpair.π₁ p, compose (kpair.π₂ p) j⟩ₖ) (by definability) (codedElementaryDiagram L M)

theorem mem_namedElementaryDiagram_iff (L M j p : V) : p ∈ namedElementaryDiagram L M j ↔
    ∃ q ∈ codedElementaryDiagram L M, p = ⟨kpair.π₁ q, compose (kpair.π₂ q) j⟩ₖ := repl_spec _

instance namedElementaryDiagram_definable : ℒₛₑₜ-function₃[V] namedElementaryDiagram := by
  have h : ℒₛₑₜ-relation₄[V] (fun D L M j ↦ ∀ p, p ∈ D ↔
      ∃ q ∈ codedElementaryDiagram L M, p = ⟨kpair.π₁ q, compose (kpair.π₂ q) j⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_namedElementaryDiagram_iff]
  rfl

theorem namedElementaryDiagram_cases {L M j p : V} (hL : IsLanguageCode L)
    (hp : p ∈ namedElementaryDiagram L M j) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ n, ∃ b ∈ structureDomain M ^ n,
      p = ⟨⟨n, φ⟩ₖ, compose b j⟩ₖ ∧ Satisfies L ∅ M ∅ n φ b := by
  obtain ⟨q, hq, rfl⟩ := (mem_namedElementaryDiagram_iff _ _ _ _).mp hp
  obtain ⟨n, hn, φ, hφ, b, hb, rfl, hs⟩ := codedElementaryDiagram_cases hL hq
  exact ⟨n, hn, φ, hφ, b, hb, by simp only [kpair.π₁_kpair, kpair.π₂_kpair], hs⟩

theorem namedElementaryDiagram_entry {L M j n φ b : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ structureDomain M ^ n) (hs : Satisfies L ∅ M ∅ n φ b) :
    ⟨⟨n, φ⟩ₖ, compose b j⟩ₖ ∈ namedElementaryDiagram L M j := by
  apply (mem_namedElementaryDiagram_iff _ _ _ _).mpr
  exact ⟨⟨⟨n, φ⟩ₖ, b⟩ₖ, (pair_mem_codedElementaryDiagram hL).mpr ⟨hφ, hb, hs⟩, by simp⟩

theorem namedElementaryDiagram_countable (hAC : InternalChoice V) {L M j : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) (hM : IsInternallyCountable (structureDomain M)) :
    IsInternallyCountable (namedElementaryDiagram L M j) :=
  internallyCountable_repl _ _ (codedElementaryDiagram_countable hAC hL hF hR hM)

theorem compose_names_retraction {A D j a n b : V} (hj : j ∈ A ^ D) (hji : Injective j)
    (ha : a ∈ D) (hb : b ∈ D ^ n) :
    compose (compose b j) (injectionRetraction j A a) = b := by
  have hr := injectionRetraction_mem_function hj hji ha
  apply function_eq_of_values (compose_function (compose_function hb hj) hr) hb
  intro i hi
  rw [value_compose_of_mem_function (compose_function hb hj) hr hi,
    value_compose_of_mem_function hb hj hi]
  exact injectionRetraction_value hj hji (function_value_mem hb hi)

theorem namedElementaryDiagram_source_realization {L M A j a : V}
    (hM : IsStructureCode L M) (hj : j ∈ A ^ structureDomain M) (hji : Injective j)
    (ha : a ∈ structureDomain M) :
    injectionRetraction j A a ∈ structureDomain M ^ A ∧
      ∀ p ∈ namedElementaryDiagram L M j,
        Satisfies L ∅ M ∅ (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p))
          (compose (kpair.π₂ p) (injectionRetraction j A a)) := by
  refine ⟨injectionRetraction_mem_function hj hji ha, fun p hp ↦ ?_⟩
  obtain ⟨n, _, φ, _, b, hb, rfl, hs⟩ := namedElementaryDiagram_cases hM.language hp
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair, compose_names_retraction hj hji ha hb] using hs

def TableRealizesNamedDiagram (L M j T : V) : Prop :=
  ∀ p ∈ namedElementaryDiagram L M j,
    TableHolds T (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p)

instance tableRealizesNamedDiagram_definable : ℒₛₑₜ-relation₄[V] TableRealizesNamedDiagram := by
  unfold TableRealizesNamedDiagram
  definability

theorem namedDiagram_quotient_elementary {M D E R j T : V}
    (hM : IsStructureCode membershipLanguageCode M) (hj : j ∈ D ^ structureDomain M)
    (hE : IsInternalSetoid D E) (hR : IsInternalRelationCongruence D E R)
    (hT : IsNameTruthTable D E R T) (hd : TableRealizesNamedDiagram membershipLanguageCode M j T) :
    IsCodedElementaryEmbedding membershipLanguageCode M (internalQuotientStructure D E R)
      (compose j (internalQuotientProjection D E)) := by
  obtain ⟨a, ha⟩ := hM.domain_nonempty
  have hD : IsNonempty D := ⟨j ‘ a, function_value_mem hj ha⟩
  apply (realizesCodedElementaryDiagram_iff hM (internalQuotientStructure_valid hD)).mp
  refine ⟨?_, fun p hp ↦ ?_⟩
  · simpa only [internalQuotientStructure_domain] using compose_function hj (internalQuotientProjection_mem D E)
  · obtain ⟨n, _, φ, hφ, b, hb, rfl, hs⟩ := codedElementaryDiagram_cases hM.language hp
    have ht := hd _ (namedElementaryDiagram_entry hM.language hφ hb hs)
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ht ⊢
    have hs' := (nameTruthTable_quotient hE hR hT n φ hφ (compose b j) (compose_function hb hj)).mp ht
    simpa only [graph_compose_assoc] using hs'

theorem namedDiagram_quotient_codedZF {M D E R j T : V}
    (hM : IsCodedZFModel M) (hj : j ∈ D ^ structureDomain M)
    (hE : IsInternalSetoid D E) (hR : IsInternalRelationCongruence D E R)
    (hT : IsNameTruthTable D E R T) (hd : TableRealizesNamedDiagram membershipLanguageCode M j T) :
    IsCodedZFModel (internalQuotientStructure D E R) :=
  ((namedDiagram_quotient_elementary hM.valid hj hE hR hT hd).isCodedZFModel_iff).mp hM

end ZFVP
