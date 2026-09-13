import ZFVP.ModelTheory.EnumeratedElementaryDiagram
import ZFVP.ModelTheory.SchmerlElementaryExtraction
import ZFVP.ModelTheory.SchmerlCodedDeadEndEquality
import ZFVP.ModelTheory.InfinitaryKeislerCompleteness

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula WithConstants)

abbrev namedDeadEndLanguage := WithConstants deadEndLanguage ℕ

def namedDeadEndEmbedding : deadEndLanguage →ᵥ namedDeadEndLanguage :=
  Language.Hom.add₁ _ _

def namedSetEmbedding : LSetC ℕ →ᵥ namedDeadEndLanguage where
  func f := match f with
    | .inl f => .inl (deadEndSetEmbedding.func f)
    | .inr f => .inr f
  rel r := match r with
    | .inl r => .inl (deadEndSetEmbedding.rel r)
    | .inr r => r.elim

/-- The countable named elementary diagram together with the full weak Rubin
sentence. Its syntax uses a fixed countable language. -/
def namedWeaklyRubinTheory {M : Type} [SetStructure M] [Nonempty M] (c : ℕ → M) :
    Set (Infinitary.Sentence namedDeadEndLanguage) :=
  (fun σ ↦ Formula.fo (σ.lMap namedSetEmbedding)) '' enumeratedDiagram c ∪
    {weaklyRubinSentence.lMap namedDeadEndEmbedding}

theorem namedWeaklyRubinTheory_countable {M : Type} [SetStructure M] [Nonempty M]
    (c : ℕ → M) : (namedWeaklyRubinTheory c).Countable :=
  ((enumeratedDiagram_countable c).image _).union (Set.countable_singleton _)

/-- A named realization retains the given model, not only its first-order theory. -/
theorem elementary_extension_of_named_realization {M N : Type}
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    [SetStructure N] [Nonempty N]
    (c : ℕ → M) (hc : Function.Surjective c) (d : ℕ → N)
    (S : Structure namedDeadEndLanguage N)
    (hS : S.lMap namedSetEmbedding = setConstStructure N d)
    (hR : (S.lMap namedDeadEndEmbedding).lMap deadEndSetEmbedding =
      (inferInstance : Structure ℒₛₑₜ N))
    (h : ∀ φ ∈ namedWeaklyRubinTheory c,
      @Formula.Eval namedDeadEndLanguage N S 0 φ Fin.elim0) :
    Nonempty (AlephOneWeaklyRubinExtension M) := by
  have hd : (setConstStructure N d).toStruc ⊧* enumeratedDiagram c := by
    apply Semantics.modelsSet_iff.mpr
    intro σ hσ
    have hh := h (.fo (σ.lMap namedSetEmbedding)) (Or.inl ⟨σ, hσ, rfl⟩)
    change (σ.lMap namedSetEmbedding).Eval (s := S) Fin.elim0 Empty.elim at hh
    rw [Semiformula.eval_lMap, hS] at hh
    exact hh
  obtain ⟨j, hj⟩ := elementaryMap_of_models_enumeratedDiagram c hc d hd
  let : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_theory_of_elementaryMap j 𝗭𝗙 inferInstance
  have hw := h (weaklyRubinSentence.lMap namedDeadEndEmbedding) (Or.inr rfl)
  have hw' := (Formula.eval_lMap namedDeadEndEmbedding S weaklyRubinSentence Fin.elim0).mp hw
  exact alephOneWeaklyRubinExtension_of_expansion j (S.lMap namedDeadEndEmbedding) hR
    (by simpa only [Matrix.empty_eq] using hw')

/-- Completeness reduces the extension theorem to syntactic consistency of
this concrete named theory. All reduct and constant interpretations are supplied here. -/
theorem elementary_extension_of_named_consistency {M : Type}
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (c : ℕ → M) (hc : Function.Surjective c)
    (hcon : Infinitary.KeislerDerivation.Consistent (namedWeaklyRubinTheory c)) :
    Nonempty (AlephOneWeaklyRubinExtension M) := by
  obtain ⟨N, hN, S, hEq, _, ht⟩ := Infinitary.KeislerDerivation.exists_standard_model
    (namedWeaklyRubinTheory c) hcon (namedWeaklyRubinTheory_countable c)
  let : Nonempty N := hN
  let : Structure namedDeadEndLanguage N := S
  let : Structure.Eq namedDeadEndLanguage N := hEq
  let : SetStructure N := ⟨fun y x ↦ S.rel (namedSetEmbedding.rel (.inl Language.Set.Rel.mem)) ![x, y]⟩
  let d : ℕ → N := fun k ↦ S.func (.inr (.const k)) ![]
  have hR : (S.lMap namedDeadEndEmbedding).lMap deadEndSetEmbedding =
      (inferInstance : Structure ℒₛₑₜ N) := by
    apply Structure.ext
    · funext k f
      exact f.elim
    · funext k r b
      cases r with
      | eq =>
          have hb : b = ![b 0, b 1] := by ext i; fin_cases i <;> rfl
          rw [hb]
          exact propext (Structure.Eq.eq (L := namedDeadEndLanguage) (b 0) (b 1))
      | mem =>
          have hb : b = ![b 0, b 1] := by ext i; fin_cases i <;> rfl
          change S.rel _ b = S.rel _ ![b 0, b 1]
          exact congrArg (S.rel _) hb
  have hS : S.lMap namedSetEmbedding = setConstStructure N d := by
    apply Structure.ext
    · funext k f b
      cases f with
      | inl f => exact f.elim
      | inr f =>
          cases f with
          | const k =>
              have hb : b = ![] := Subsingleton.elim _ _
              subst b
              rfl
    · funext k r b
      cases r with
      | inl r => exact congrArg (fun T : Structure ℒₛₑₜ N ↦ T.rel r b) hR
      | inr r => exact r.elim
  exact elementary_extension_of_named_realization c hc d S hS hR ht

end ZFVP.Schmerl



