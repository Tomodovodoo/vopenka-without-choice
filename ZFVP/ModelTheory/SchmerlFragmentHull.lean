import ZFVP.ModelTheory.SchmerlElementaryFragmentCoding
import ZFVP.ModelTheory.SchmerlUniverseFragmentCoding
import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.SetTheory.ChoiceDictionary
import ZFVP.ModelTheory.ElementaryLanguageSymbols
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

/-! A countable elementary hull containing the represented support of a
proof. Its represented fragment is transported by explicit constructor laws. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory ZFVP.Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language}
variable (L H : V) (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
  (C : {n : ℕ} → Formula Λ n → V) (A : Set (Σ n, Formula Λ n)) (S : Set V)

def codingSeed : Set V := ({L, H} ∪ S) ∪
  Set.range (fun f : Σ k, Λ.Func k ↦ F f.2) ∪
  Set.range (fun r : Σ k, Λ.Rel k ↦ R r.2) ∪ (fun a : Σ n, Formula Λ n ↦ C a.2) '' A

abbrev CodingHull := Hull (codingSeed L H F R C A S)

instance codingHull_zf : (CodingHull L H F R C A S)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  (inferInstance : CodingHull L H F R C A S ≡ₑ[ℒₛₑₜ] V).modelsTheory.mpr inferInstance

noncomputable def codingHullMap : ZFVP.ElementaryMap (CodingHull L H F R C A S) V where
  toFun := Subtype.val
  elementary φ b f := elementary_of_semisentences Subtype.val
    (fun ψ c ↦ Hull.hull_models_iff (s := codingSeed L H F R C A S) (φ := ψ) (b := c)) φ b f

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codingSeed_countable [Countable (Σ k, Λ.Func k)] [Countable (Σ k, Λ.Rel k)]
    (hA : A.Countable) (hS : S.Countable) : (codingSeed L H F R C A S).Countable :=
  ((((Set.to_countable {L, H}).union hS).union (Set.countable_range _)).union
    (Set.countable_range _)).union (hA.image _)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codingHull_countable [Countable (Σ k, Λ.Func k)] [Countable (Σ k, Λ.Rel k)]
    (hA : A.Countable) (hS : S.Countable) : Countable (CodingHull L H F R C A S) := by
  let := (codingSeed_countable L H F R C A S hA hS).to_subtype
  infer_instance

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codingHull_seed {x : V} (hx : x ∈ S) : x ∈ CodingHull L H F R C A S := by
  apply Hull.subset
  exact Or.inl (Or.inl (Or.inl (Or.inr hx)))

noncomputable def codingHullLanguage : CodingHull L H F R C A S :=
  ⟨L, Hull.subset _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))⟩

noncomputable def codingHullFragment : CodingHull L H F R C A S :=
  ⟨H, Hull.subset _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))⟩

noncomputable def codingHullFunction {k} (f : Λ.Func k) : CodingHull L H F R C A S :=
  ⟨F f, Hull.subset _ (Or.inl (Or.inl (Or.inr ⟨⟨k, f⟩, rfl⟩)))⟩

noncomputable def codingHullRelation {k} (r : Λ.Rel k) : CodingHull L H F R C A S :=
  ⟨R r, Hull.subset _ (Or.inl (Or.inr ⟨⟨k, r⟩, rfl⟩))⟩

noncomputable def codingHullFormula {n} (φ : Formula Λ n) : CodingHull L H F R C A S := by
  classical
  exact if hφ : ⟨n, φ⟩ ∈ A then
    ⟨C φ, Hull.subset _ (Or.inr ⟨⟨n, φ⟩, hφ, rfl⟩)⟩ else ∅

theorem codingHullFormula_val {n} (φ : Formula Λ n) (hφ : ⟨n, φ⟩ ∈ A) :
    (codingHullFormula L H F R C A S φ).val = C φ := by
  simp [codingHullFormula, hφ]

theorem codingHull_coding (h : IsFragmentCoding L H F R C A) :
    IsFragmentCoding (codingHullLanguage L H F R C A S) (codingHullFragment L H F R C A S)
      (codingHullFunction L H F R C A S) (codingHullRelation L H F R C A S)
      (codingHullFormula L H F R C A S) A := by
  apply IsFragmentCoding.of_map_elementary (codingHullMap L H F R C A S)
  exact h.congrCode (codingHullFormula_val L H F R C A S)

theorem codingHull_standardOmega (hω : HasStandardOmega V) :
    HasStandardOmega (CodingHull L H F R C A S) :=
  standardOmega_of_elementaryMap (codingHullMap L H F R C A S) hω

theorem codingHull_choice (hAC : InternalChoice V) : InternalChoice (CodingHull L H F R C A S) :=
  (codingHullMap L H F R C A S).internalChoice_iff.mpr hAC

theorem codingHullFragment_countable (hH : IsInternallyCountable H) :
    IsInternallyCountable (codingHullFragment L H F R C A S) :=
  ((codingHullMap L H F R C A S).map_internallyCountable_iff _).mp hH

theorem codingHull_function_valid
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V)) :
    ∀ k (f : Λ.Func k), codingHullFunction L H F R C A S f ∈
      functionSymbols (codingHullLanguage L H F R C A S) ∧
      (functionArities (codingHullLanguage L H F R C A S)) ‘ (codingHullFunction L H F R C A S f) = k :=
  ((codingHullMap L H F R C A S).functionRepresentation_iff _ _).mp hF

theorem codingHull_relation_valid
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V)) :
    ∀ k (r : Λ.Rel k), codingHullRelation L H F R C A S r ∈
      relationSymbols (codingHullLanguage L H F R C A S) ∧
      (relationArities (codingHullLanguage L H F R C A S)) ‘ (codingHullRelation L H F R C A S r) = k :=
  ((codingHullMap L H F R C A S).relationRepresentation_iff _ _).mp hR

end ZFVP.Infinitary.Internal


