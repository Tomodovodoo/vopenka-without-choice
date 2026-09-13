import ZFVP.SetTheory.CheckNameTables

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCheckNameValueFormula : SetTheorySemisentence 5 :=
  “one T f u y. (∀ z ∈ y, ∃ s ∈ u, ∃ v ∈ T, !boundedPairMemberFormula f s v ∧ !boundedKpairFormula z v one) ∧
    (∀ s ∈ u, ∃ v ∈ T, !boundedPairMemberFormula f s v ∧ !boundedPairMemberFormula y v one)”

def boundedCheckNameTableFormula : SetTheorySemisentence 4 :=
  “one C T f. !boundedFunctionFormula f C T ∧ ∀ u ∈ C, ∀ y ∈ T,
    !boundedPairMemberFormula f u y → !boundedCheckNameValueFormula one T f u y”

theorem boundedCheckNameValueFormula_bounded : IsBoundedSetFormula boundedCheckNameValueFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact boundedKpairFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem boundedCheckNameTableFormula_bounded : IsBoundedSetFormula boundedCheckNameTableFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 1) (.all (.bvar 3)
    (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedCheckNameValueFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedCheckNameValueFormula {C T f u : V} [hC : IsTransitive C]
    (hf : f ∈ T ^ C) (hu : u ∈ C) (one y : V) :
    boundedCheckNameValueFormula.Evalb ![one, T, f, u, y] ↔
      ∀ z, z ∈ y ↔ ∃ s ∈ u, z = ⟨f ‘ s, one⟩ₖ := by
  simp only [boundedCheckNameValueFormula]
  simp
  have he (s : V) (hs : s ∈ u) (Q : V → Prop) := exists_function_pair_value_iff hf (hC.mem_trans hs hu) Q
  simp +contextual only [he]
  constructor
  · rintro ⟨hl, hr⟩ z
    constructor
    · intro hz
      obtain ⟨s, hs, hv⟩ := hl z hz
      exact ⟨s, hs, (he s hs (fun v ↦ z = ⟨v, one⟩ₖ)).mp hv⟩
    · rintro ⟨s, hs, rfl⟩
      exact hr s hs
  · intro h
    refine ⟨?_, fun s hs ↦ (h _).mpr ⟨s, hs, rfl⟩⟩
    intro z hz
    obtain ⟨s, hs, hz⟩ := (h z).mp hz
    exact ⟨s, hs, (he s hs (fun v ↦ z = ⟨v, one⟩ₖ)).mpr hz⟩

theorem eval_boundedCheckNameTableFormula (one C T f : V) [IsTransitive C] :
    boundedCheckNameTableFormula.Evalb ![one, C, T, f] ↔ IsCheckNameTable one C T f := by
  simp only [boundedCheckNameTableFormula, IsCheckNameTable]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  intro hf
  let := IsFunction.of_mem hf
  constructor
  · intro h u hu
    exact (eval_boundedCheckNameValueFormula hf hu one (f ‘ u)).mp
      (h u hu (f ‘ u) (function_value_mem hf hu)
        (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hu)))
  · intro h u hu y _ huy
    have he : f ‘ u = y := value_eq_of_kpair_mem huy
    exact (eval_boundedCheckNameValueFormula hf hu one y).mpr (he ▸ h u hu)

end ZFVP
