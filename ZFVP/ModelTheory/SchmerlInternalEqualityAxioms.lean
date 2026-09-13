import ZFVP.ModelTheory.SchmerlInternalInstantiation
import ZFVP.ModelTheory.SchmerlInternalFOCoherence
import ZFVP.ModelTheory.SchmerlInternalQTwoPoints

/-! Logical equality for arbitrary terms, substitutivity in actual
infinitary formulas, and the nonempty-domain axiom. The latter is explicit
even for relational languages with no closed terms. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def termPairArguments (t u : V) : V := standardTuple ![t, u]

instance termPairArguments_definable : ℒₛₑₜ-function₂[V] termPairArguments := by
  unfold termPairArguments standardTuple
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

noncomputable def termEqualityCode (t u : V) : V := foCode (atomCode equalityToken (termPairArguments t u))

instance termEqualityCode_definable : ℒₛₑₜ-function₂[V] termEqualityCode := by
  unfold termEqualityCode equalityToken
  definability

theorem holds_termEqualityCode {L F M n t u b : V} (hF : IsFragment L F)
    (hc : ⟨n, termEqualityCode t u⟩ₖ ∈ F) (ht : t ∈ termSet L ∅ n) (hu : u ∈ termSet L ∅ n)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (termEqualityCode t u) b ↔
      (termEvaluation L ∅ n M b ∅) ‘ t = (termEvaluation L ∅ n M b ∅) ‘ u := by
  have hn := (hF.node hc).1
  have ha : IsAtomicArguments L ∅ n equalityToken (termPairArguments t u) := by
    refine Or.inl ⟨rfl, ?_⟩
    apply standardTuple_mem_function
    intro i
    exact Fin.cases ht (fun j ↦ Fin.cases hu (fun k ↦ Fin.elim0 k) j) i
  have he : evaluatedArguments L ∅ M ∅ n b (termPairArguments t u) =
      standardTuple ![(termEvaluation L ∅ n M b ∅) ‘ t, (termEvaluation L ∅ n M b ∅) ‘ u] := by
    unfold evaluatedArguments evaluateWithFreeAssignment termPairArguments
    rw [compose_standardTuple]
    · congr 1
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    · intro i
      simp only [domain_termEvaluation]
      exact Fin.cases ht (fun j ↦ Fin.cases hu (fun k ↦ Fin.elim0 k) j) i
  rw [termEqualityCode, holds_fo hF hc, satisfies_atom hF.1 hn ha hb, atomicHolds_equality, he]
  change (standardTuple ![(termEvaluation L ∅ n M b ∅) ‘ t, (termEvaluation L ∅ n M b ∅) ‘ u]) ‘
    (((0 : Fin 2).val : ℕ) : V) =
    (standardTuple ![(termEvaluation L ∅ n M b ∅) ‘ t, (termEvaluation L ∅ n M b ∅) ‘ u]) ‘
    (((1 : Fin 2).val : ℕ) : V) ↔ _
  simp only [value_standardTuple]
  rfl

def IsEqualityAxiom (L n χ : V) : Prop := IsLanguageCode L ∧ n ∈ (ω : V) ∧
  ((∃ t, t ∈ termSet L ∅ n ∧ χ = termEqualityCode t t) ∨
  (∃ H φ t u, IsFragment L H ∧ ⟨succ n, φ⟩ₖ ∈ H ∧
    t ∈ termSet L ∅ n ∧ u ∈ termSet L ∅ n ∧
    χ = impCode (termEqualityCode t u)
      (equivCode (instantiateCode L H n t φ) (instantiateCode L H n u φ))) ∨
  χ = exsCode (equalityCode 0 0))

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

instance isEqualityAxiom_definable : ℒₛₑₜ-relation₃[V] IsEqualityAxiom := by
  unfold IsEqualityAxiom
  apply Language.Definable.and (by definability)
  apply Language.Definable.and (by definability)
  repeat' apply Language.Definable.or
  all_goals definability

theorem IsEqualityAxiom.sound {L F M n χ b : V} (hχ : IsEqualityAxiom L n χ)
    (hF : IsFragment L F) (hM : IsStructureCode L M) (hc : ⟨n, χ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) : Holds L F M n χ b := by
  obtain ⟨_, hn, hχ⟩ := hχ
  rcases hχ with ⟨t, ht, rfl⟩ | ⟨H, φ, t, u, hH, hφ, ht, hu, rfl⟩ | rfl
  · exact (holds_termEqualityCode hF hc ht ht hb).mpr rfl
  · have he := hF.imp_left_mem hc
    have hi := hF.imp_right_mem hc
    rw [holds_imp hF hc hb, holds_termEqualityCode hF he ht hu hb, holds_equiv hF hi hb,
      holds_instantiateCode hH hF hM hn ht hφ (hF.equiv_left_mem hi) hb,
      holds_instantiateCode hH hF hM hn hu hφ (hF.equiv_right_mem hi) hb]
    intro h
    rw [h]
  · obtain ⟨x, hx⟩ := hM.domain_nonempty.nonempty
    apply (holds_exs hF hc hb).mpr
    refine ⟨x, hx, ?_⟩
    exact (holds_equalityCode hF (hF.exs_mem hc) (zero_mem_succ_natural hn)
      (zero_mem_succ_natural hn) (assignmentPrepend_mem_function hn hb hx)).mpr rfl

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_termPairArguments (t u : V) : j (termPairArguments t u) = termPairArguments (j t) (j u) := by
  unfold termPairArguments
  rw [j.map_standardTuple]
  congr 1
  funext i
  exact Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) i

theorem map_termEqualityCode (t u : V) : j (termEqualityCode t u) = termEqualityCode (j t) (j u) := by
  simp only [termEqualityCode, map_foCode, j.map_atomCode, j.map_equalityToken, map_termPairArguments]

theorem equalityAxiom_map {L n χ : V} (hχ : IsEqualityAxiom L n χ) :
    IsEqualityAxiom (j L) (j n) (j χ) := by
  obtain ⟨hL, hn, hχ⟩ := hχ
  have ht {t : V} (ht : t ∈ termSet L ∅ n) : j t ∈ termSet (j L) ∅ (j n) := by
    simpa only [j.map_termSet hL hn, j.map_empty] using (j.mem_iff _ _).mpr ht
  refine ⟨(j.languageCode_iff L).mpr hL, (j.natural_iff _).mpr hn, ?_⟩
  rcases hχ with ⟨t, ht', rfl⟩ | ⟨H, φ, t, u, hH, hφ, ht', hu, rfl⟩ | rfl
  · exact Or.inl ⟨j t, ht ht', map_termEqualityCode j t t⟩
  · refine Or.inr (Or.inl ⟨j H, j φ, j t, j u, fragment_map j hH, ?_, ht ht', ht hu, ?_⟩)
    · simpa only [j.map_kpair, j.map_succ] using (j.mem_iff _ _).mpr hφ
    · rw [map_impCode, map_termEqualityCode, map_equivCode,
        map_instantiateCode j hH hn ht', map_instantiateCode j hH hn hu]
  · exact Or.inr (Or.inr (by simp only [map_exsCode, map_equalityCode,
      (show j (0 : V) = (0 : W) from j.map_numeral 0)]))

end EndExtension
end ZFVP.Infinitary.Internal
