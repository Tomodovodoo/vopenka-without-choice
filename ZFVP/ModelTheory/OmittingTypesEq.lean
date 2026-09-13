import ZFVP.ModelTheory.TermModel
import ZFVP.ModelTheory.StageType

/-! # The omitting types theorem for languages with equality

A consistent theory `T` in a countable language with equality, containing the equality axioms
`𝗘𝗤 L`, which locally omits each of countably many types has a countable model omitting all of
them. The proof is the Henkin construction of `ZFVP.ModelTheory.HenkinSet`, whose omitting
requirement is met by `ZFVP.exists_omit_consistentOver`, followed by the term model of
`ZFVP.ModelTheory.TermModel`.

The equality hypothesis is not cosmetic. `ZFVP.OmittingTypesTheorem`, the same statement for an
arbitrary language, is false: without equality the term model has elements, such as the value of a
function symbol, that no witness variable names, and a type can be realized there. The refutation
is `ZFVP.ModelTheory.OmittingTypesCounterexample`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u w

/-- The omitting types theorem for languages with equality, as a named `Prop`: a consistent theory
containing the equality axioms which locally omits each of countably many types has a countable
model omitting all of them. -/
def OmittingTypesTheoremEq : Prop :=
  ∀ (L : Language.{w}) [L.Encodable] [L.Eq] (T : Theory L), 𝗘𝗤 L ⊆ T → Consistent T →
    ∀ (q : ℕ → ℕ) (Ψ : (n : ℕ) → PartialType L (q n)),
      (∀ n, LocallyOmits T (Ψ n)) → Nonempty (OmittingModel T Ψ)

/-- The omitting types theorem for languages with equality. -/
theorem omittingTypesTheoremEq : OmittingTypesTheoremEq.{u} := by
  intro L _ _ T hEq hcon q Ψ hloc
  obtain ⟨H⟩ := exists_henkinSet T hcon Ψ
    fun n a ha Δ hΔ ↦ exists_omit_consistentOver (hloc n) a ha Δ hΔ
  exact ⟨omittingModel hEq H⟩

/-- The single type case, read off the countable family case by taking a constant family. -/
theorem omittingModel_of_omittingTypesTheoremEq (L : Language.{u}) [L.Encodable] [L.Eq]
    (T : Theory L) (hEq : 𝗘𝗤 L ⊆ T) (hT : Consistent T) {q : ℕ} (Ψ : PartialType L q)
    (hΨ : LocallyOmits T Ψ) :
    Nonempty (OmittingModel T (ι := ℕ) (q := fun _ ↦ q) fun _ ↦ Ψ) :=
  omittingTypesTheoremEq L T hEq hT (fun _ ↦ q) (fun _ ↦ Ψ) fun _ ↦ hΨ

end ZFVP
