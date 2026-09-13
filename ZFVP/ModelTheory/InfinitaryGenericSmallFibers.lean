import ZFVP.ModelTheory.InfinitaryGenericElementarity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

/-- A coordinate term in an old small fiber equals an old closed term. -/
theorem termClass_eq_oldTerm_of_small {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hs : .q ψ ∉ H.carrier) (t : CoordinateTerm (limit L))
    (he : CoordinateTerm.Eval C.point ψ (fun _ : Fin 1 ↦ t)) :
    ∃ u : Semiterm (limit L) Empty 0, C.termClass t = C.oldTerm u := by
  obtain ⟨i, hi⟩ := he
  obtain ⟨j, hj⟩ := C.freezes t.2 ψ hψ hs
  obtain ⟨ht, hf⟩ := hj (max i j) (Nat.le_max_right _ _)
  obtain ⟨hv, hh⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_left i j)) hi
  rcases hf with hf | ⟨u, hu⟩
  · obtain ⟨b, hb⟩ := (C.point (max i j)).realizable
    have heq : (fun a : Fin 1 ↦ t.2.val (b ∘ Formula.rightEmbed (hv a)) Empty.elim) =
        t.2.val (b ∘ Formula.rightEmbed ht) Empty.elim :> Fin.elim0 := by
      funext a
      fin_cases a
      rfl
    exact ((hf b hb) (heq ▸ hh b hb)).elim
  · refine ⟨u, (C.termClass_eq_iff t ⟨0, u⟩).mpr ?_⟩
    refine ⟨max i j, ht, Nat.zero_le _, ?_⟩
    intro b hb
    simpa only [show b ∘ Formula.rightEmbed (Nat.zero_le (1 + (C.point (max i j)).1)) =
      Fin.elim0 from Subsingleton.elim _ _] using hu b hb

/-- The actual extension adds no points to an old small unary fiber. -/
theorem small_fiber_subset_oldRange {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hs : .q ψ ∉ H.carrier) :
    {y : C.ExtensionDomain | Formula.WeakEval C.extensionQuantifier ψ (y :> Fin.elim0)} ⊆
      Set.range C.oldEmbedding := by
  intro y hy
  obtain ⟨t, rfl⟩ := C.termClass_surjective y
  have he : CoordinateTerm.Eval C.point ψ (fun _ : Fin 1 ↦ t) := by
    apply (C.extension_truth ψ hψ (fun _ : Fin 1 ↦ t)).mp
    have heq : (fun _ : Fin 1 ↦ C.termClass t) = C.termClass t :> Fin.elim0 := by
      funext a
      fin_cases a
      rfl
    exact heq ▸ hy
  obtain ⟨u, hu⟩ := C.termClass_eq_oldTerm_of_small hψ hs t he
  exact ⟨H.classOf u, (C.oldEmbedding_classOf u).trans hu.symm⟩

theorem small_fiber_eq_oldImage {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hs : .q ψ ∉ H.carrier) :
    {y : C.ExtensionDomain | Formula.WeakEval C.extensionQuantifier ψ (y :> Fin.elim0)} =
      C.oldEmbedding '' {x : H.Domain | Formula.WeakEval H.weakQuantifier ψ (x :> Fin.elim0)} := by
  have helem (x : H.Domain) :
      Formula.WeakEval C.extensionQuantifier ψ (C.oldEmbedding x :> Fin.elim0) ↔
        Formula.WeakEval H.weakQuantifier ψ (x :> Fin.elim0) := by
    have heq : C.oldEmbedding ∘ (x :> Fin.elim0) = C.oldEmbedding x :> Fin.elim0 := by
      funext a
      fin_cases a
      rfl
    simpa only [heq] using C.extension_elementary ψ hψ (x :> Fin.elim0)
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := C.small_fiber_subset_oldRange hψ hs hy
    exact ⟨x, (helem x).mp hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (helem x).mpr hx

theorem small_fiber_eq_oldImage_of_not_q {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hs : ¬Formula.WeakEval H.weakQuantifier (.q ψ) Fin.elim0) :
    {y : C.ExtensionDomain | Formula.WeakEval C.extensionQuantifier ψ (y :> Fin.elim0)} =
      C.oldEmbedding '' {x : H.Domain | Formula.WeakEval H.weakQuantifier ψ (x :> Fin.elim0)} :=
  C.small_fiber_eq_oldImage hψ
    (fun hq ↦ hs ((H.weak_sentence_truth (.q ψ) (q_closed hψ)).mpr hq))

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
