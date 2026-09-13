import ZFVP.ModelTheory.SchmerlWeaklyRubinExtraction
import ZFVP.ModelTheory.CountabilityEssential
import ZFVP.ModelTheory.FiniteParameterElementarity

/-! The size reduction can retain a prescribed countable elementary submodel.
The hull is first-order elementary and contains the image of that model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

/-- An actual expansion satisfying Φ⁺ gives the exact elementary-extension
object used in the countability-essential theorem, retaining a specified
countable elementary submodel. -/
theorem alephOneWeaklyRubinExtension_of_expansion {M V : Type}
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (e : ElementaryMap M V) (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![]) :
    Nonempty (AlephOneWeaklyRubinExtension M) := by
  let : Structure deadEndLanguage V := S
  let seed : Set V := Set.range e
  let A := Infinitary.DownwardLS.hull weaklyRubinSentence seed
  let : SetStructure A := closedSubsetSetStructure A
  let : Nonempty A := Infinitary.DownwardLS.hullNonempty _ seed
  have hAS := closedSubset_set_reduct S hS A
  have hi {n : ℕ} (ψ : SetTheorySemisentence n) (b : Fin n → A) :
      ψ.Evalb b ↔ ψ.Evalb (fun i ↦ (b i : V)) := by
    calc
      _ ↔ (ψ.lMap deadEndSetEmbedding).Evalb (s := A.toStructure) b :=
        (eval_functionOriginal_of_reduct deadEndSetEmbedding A.toStructure hAS ψ b).symm
      _ ↔ (ψ.lMap deadEndSetEmbedding).Evalb (s := S) (fun i ↦ (b i : V)) :=
        Infinitary.DownwardLS.firstOrder_eval weaklyRubinSentence seed _ b
      _ ↔ _ := eval_functionOriginal_of_reduct deadEndSetEmbedding S hS ψ _
  have hAZF : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
    apply models_theory_iff.mpr
    intro ψ hψ
    have hv := Theory.models V 𝗭𝗙 hψ
    change ψ.Evalb ![] at hv ⊢
    exact (hi ψ ![]).mpr (by simpa only [Matrix.empty_eq] using hv)
  let : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hAZF
  have hA : @Formula.Eval deadEndLanguage A A.toStructure 0 weaklyRubinSentence ![] :=
    (Infinitary.DownwardLS.sentence_eval _ seed).mpr h
  have hseed : Cardinal.mk seed ≤ Cardinal.aleph 1 := by
    let : Countable seed := (Set.countable_range e).to_subtype
    exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_lt_aleph_one.le
  have hcard : Cardinal.mk A = Cardinal.aleph 1 :=
    le_antisymm (Infinitary.DownwardLS.hull_card_le _ seed hseed)
      (aleph_one_le_of_deadEndSentence A.toStructure ((Formula.eval_and _ _ _).mp hA).1)
  let f : M → A := fun m ↦ ⟨e m, Infinitary.DownwardLS.subset_hull _ seed ⟨m, rfl⟩⟩
  have hf {n : ℕ} (ψ : SetTheorySemisentence n) (b : Fin n → M) :
      ψ.Evalb b ↔ ψ.Evalb (f ∘ b) := by
    have he := e.elementary ψ b (Empty.elim : Empty → M)
    have hi' := hi ψ (f ∘ b)
    have he' : ψ.Evalb b ↔ ψ.Evalb (fun i ↦ e (b i)) := by
      simpa only [Semiformula.Evalb, Function.comp_def, Empty.eq_elim] using he
    exact he'.trans hi'.symm
  let j : ElementaryMap M A := ⟨f, elementary_of_semisentences f hf⟩
  exact ⟨{ Model := A
           card := hcard
           weaklyRubin := isWeaklyRubin_of_weaklyRubinSentence A.toStructure hAS hA hcard.le
           embedding := j }⟩

end ZFVP.Schmerl
