import ZFVP.SetTheory.NameActionTables

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNameActionValueFormula : SetTheorySemisentence 7 :=
  “P π C T f u y.
    (∀ z ∈ y, ∃ s ∈ C, ∃ p ∈ P, !boundedPairMemberFormula u s p ∧
      ∃ v ∈ T, !boundedPairMemberFormula f s v ∧ ∃ q ∈ P,
        !boundedPairMemberFormula π p q ∧ !boundedKpairFormula z v q) ∧
    (∀ s ∈ C, ∀ p ∈ P, !boundedPairMemberFormula u s p →
      ∃ v ∈ T, !boundedPairMemberFormula f s v ∧ ∃ q ∈ P,
        !boundedPairMemberFormula π p q ∧ !boundedPairMemberFormula y v q)”

def boundedNameActionTableFormula : SetTheorySemisentence 5 :=
  “P π C T f. !boundedFunctionFormula f C T ∧ ∀ u ∈ C, ∀ y ∈ T,
    !boundedPairMemberFormula f u y → !boundedNameActionValueFormula P π C T f u y”

theorem boundedNameActionValueFormula_bounded : IsBoundedSetFormula boundedNameActionValueFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedKpairFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedNameActionTableFormula_bounded : IsBoundedSetFormula boundedNameActionTableFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 2) (.all (.bvar 4)
    (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedNameActionValueFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_function_pair_value_iff {f A B x : V} (hf : f ∈ B ^ A) (hx : x ∈ A) (Q : V → Prop) :
    (∃ y ∈ B, ⟨x, y⟩ₖ ∈ f ∧ Q y) ↔ Q (f ‘ x) := by
  let := IsFunction.of_mem hf
  constructor
  · rintro ⟨y, _, hxy, hy⟩
    exact (value_eq_of_kpair_mem hxy).symm ▸ hy
  · intro h
    exact ⟨f ‘ x, function_value_mem hf hx,
      kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hx), h⟩

theorem eval_boundedNameActionValueFormula {P π C T f : V} (hπ : π ∈ P ^ P) (hf : f ∈ T ^ C)
    (u y : V) : boundedNameActionValueFormula.Evalb ![P, π, C, T, f, u, y] ↔
      ∀ z, z ∈ y ↔ ∃ s ∈ C, ∃ p ∈ P, ⟨s, p⟩ₖ ∈ u ∧ z = ⟨f ‘ s, π ‘ p⟩ₖ := by
  have he (s p : V) (hs : s ∈ C) (hp : p ∈ P) (Q : V → V → Prop) :
      (∃ v ∈ T, ⟨s, v⟩ₖ ∈ f ∧ ∃ q ∈ P, ⟨p, q⟩ₖ ∈ π ∧ Q v q) ↔ Q (f ‘ s) (π ‘ p) := by
    rw [exists_function_pair_value_iff hf hs]
    exact exists_function_pair_value_iff hπ hp _
  simp only [boundedNameActionValueFormula]
  simp
  simp +contextual only [he]
  constructor
  · rintro ⟨hleft, hright⟩ z
    constructor
    · intro hz
      obtain ⟨s, hs, p, hp, hsp, hv⟩ := hleft z hz
      exact ⟨s, hs, p, hp, hsp, (he s p hs hp (fun v q ↦ z = ⟨v, q⟩ₖ)).mp hv⟩
    · rintro ⟨s, hs, p, hp, hsp, rfl⟩
      exact hright s hs p hp hsp
  · intro h
    refine ⟨?_, fun s hs p hp hsp ↦ (h _).mpr ⟨s, hs, p, hp, hsp, rfl⟩⟩
    intro z hz
    obtain ⟨s, hs, p, hp, hsp, hz⟩ := (h z).mp hz
    exact ⟨s, hs, p, hp, hsp, (he s p hs hp (fun v q ↦ z = ⟨v, q⟩ₖ)).mpr hz⟩

theorem eval_boundedNameActionTableFormula {P π : V} (hπ : π ∈ P ^ P) (C T f : V) :
    boundedNameActionTableFormula.Evalb ![P, π, C, T, f] ↔ IsNameActionTable P π C T f := by
  simp only [boundedNameActionTableFormula, IsNameActionTable]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  intro hf
  let := IsFunction.of_mem hf
  constructor
  · intro h u hu
    exact (eval_boundedNameActionValueFormula hπ hf u (f ‘ u)).mp
      (h u hu (f ‘ u) (function_value_mem hf hu)
        (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hu)))
  · intro h u hu y _ huy
    have he : f ‘ u = y := value_eq_of_kpair_mem huy
    exact (eval_boundedNameActionValueFormula hπ hf u y).mpr (he ▸ h u hu)

end ZFVP
