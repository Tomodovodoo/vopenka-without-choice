import ZFVP.SetTheory.DeltaOneWoodinSeedMatrix
import ZFVP.SetTheory.WoodinSeedSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSourceColumnCertificate (φ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  “G θ Q. ∃ D, !sigmaOneWoodinSourceIndexFormula D θ ∧ !(graphAssemblyFormula φ) G D Q”

def woodinSourceColumnPiCertificate (φ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  “G θ Q. !IsOrdinal.dfn θ ∧ ∀ H, !(woodinSourceColumnCertificate φ) H θ Q → G = H”

theorem woodinSourceColumnCertificate_sigmaOne {φ : SetTheorySemisentence 3} (hφ : IsSigmaFormula 1 φ) :
    IsSigmaFormula 1 (woodinSourceColumnCertificate φ) :=
  .exs (.and (sigmaOneWoodinSourceIndexFormula_sigmaOne.subst _) ((graphAssemblyFormula_levy hφ).subst _))

theorem woodinSourceColumnPiCertificate_piOne {φ : SetTheorySemisentence 3} (hφ : IsSigmaFormula 1 φ) :
    IsPiFormula 1 (woodinSourceColumnPiCertificate φ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or ((woodinSourceColumnCertificate_sigmaOne hφ).subst _).neg (.bounded (.rel _ _))))

def sigmaOneWoodinSeedProjectionRow : SetTheorySemisentence 3 :=
  “y j Q. ∃ q, !boundedValueFormula q Q j ∧ ∃ e, !boundedEmptyFormula e ∧
    ∃ s, !boundedSingletonFormula s e ∧ !boundedProductFormula y q s”

def sigmaOneWoodinSeedSectionRow : SetTheorySemisentence 3 :=
  “y j t. ∃ q, !boundedValueFormula q t j ∧ ∃ e, !boundedEmptyFormula e ∧
    ∃ s, !boundedSingletonFormula s e ∧ ∃ u, !boundedSingletonFormula u q ∧ !boundedProductFormula y s u”

def sigmaOneWoodinSeedLiftMapFormula : SetTheorySemisentence 2 :=
  “G Q. ∃ e, !boundedEmptyFormula e ∧ ∃ s, !boundedSingletonFormula s e ∧
    ∃ D, !boundedProductFormula D Q s ∧ !(graphAssemblyFormula sigmaOnePairFirstFormula) G D”

def sigmaOneWoodinSeedLiftRow : SetTheorySemisentence 3 :=
  “y j Q. ∃ q, !boundedValueFormula q Q j ∧ !sigmaOneWoodinSeedLiftMapFormula y q”

def sigmaOneWoodinSeedProjectionColumnFormula : SetTheorySemisentence 3 :=
  woodinSourceColumnCertificate sigmaOneWoodinSeedProjectionRow

def sigmaOneWoodinSeedSectionColumnFormula : SetTheorySemisentence 3 :=
  woodinSourceColumnCertificate sigmaOneWoodinSeedSectionRow

def sigmaOneWoodinSeedLiftColumnFormula : SetTheorySemisentence 3 :=
  woodinSourceColumnCertificate sigmaOneWoodinSeedLiftRow

theorem sigmaOneWoodinSeedProjectionRow_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedProjectionRow :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      (.exs (.bounded (.and (boundedSingletonFormula_bounded.subst _) (boundedProductFormula_bounded.subst _)))))))

theorem sigmaOneWoodinSeedSectionRow_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedSectionRow :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
        (.exs (.bounded (.and (boundedSingletonFormula_bounded.subst _) (boundedProductFormula_bounded.subst _)))))))))

theorem sigmaOneWoodinSeedLiftMapFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedLiftMapFormula :=
  .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
      (.exs (.and (.bounded (boundedProductFormula_bounded.subst _))
        ((graphAssemblyFormula_levy sigmaOnePairFirstFormula_sigmaOne).subst _))))))

theorem sigmaOneWoodinSeedLiftRow_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedLiftRow :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (sigmaOneWoodinSeedLiftMapFormula_sigmaOne.subst _))

theorem sigmaOneWoodinSeedProjectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedProjectionColumnFormula :=
  woodinSourceColumnCertificate_sigmaOne sigmaOneWoodinSeedProjectionRow_sigmaOne

theorem sigmaOneWoodinSeedSectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedSectionColumnFormula :=
  woodinSourceColumnCertificate_sigmaOne sigmaOneWoodinSeedSectionRow_sigmaOne

theorem sigmaOneWoodinSeedLiftColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedLiftColumnFormula :=
  woodinSourceColumnCertificate_sigmaOne sigmaOneWoodinSeedLiftRow_sigmaOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinSourceColumnCertificate_defined (c : V → V → V) (φ : SetTheorySemisentence 3)
    [hc : ℒₛₑₜ-function₂ c via φ] :
    ℒₛₑₜ-relation₃ (fun G θ Q ↦ IsOrdinal θ ∧ G = definableGraph (woodinSourceIndex θ)
      (fun j ↦ c j Q) (by have := hc.to_definable; definability)) via woodinSourceColumnCertificate φ :=
  ⟨fun v ↦ by
    have he := fun D ↦ eval_graphAssemblyFormula φ (v 0) D ![v 2] (fun j ↦ c j (v 2))
      (by have := hc.to_definable; definability) (fun x _ y ↦ by simp)
    simp only [Semiformula.Evalb] at he
    simp [woodinSourceColumnCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he]⟩

instance woodinSourceColumnPiCertificate_defined (c : V → V → V) (φ : SetTheorySemisentence 3)
    [hc : ℒₛₑₜ-function₂ c via φ] :
    ℒₛₑₜ-relation₃ (fun G θ Q ↦ IsOrdinal θ ∧ G = definableGraph (woodinSourceIndex θ)
      (fun j ↦ c j Q) (by have := hc.to_definable; definability)) via woodinSourceColumnPiCertificate φ :=
  ⟨fun v ↦ by
    simp [woodinSourceColumnPiCertificate]
    intro h
    simp only [h, true_implies]
    constructor
    · intro hh
      exact hh _ rfl
    · intro hh x hx
      exact hh.trans hx.symm⟩

instance sigmaOneWoodinSeedProjectionRow_defined :
    ℒₛₑₜ-function₂[V] (fun j Q ↦ (Q ‘ j) ×ˢ ({∅} : V)) via sigmaOneWoodinSeedProjectionRow :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedProjectionRow]⟩

instance sigmaOneWoodinSeedSectionRow_defined :
    ℒₛₑₜ-function₂[V] (fun j t ↦ ({∅} : V) ×ˢ {t ‘ j}) via sigmaOneWoodinSeedSectionRow :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedSectionRow]⟩

instance sigmaOneWoodinSeedLiftMapFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSeedLiftMap via sigmaOneWoodinSeedLiftMapFormula :=
  ⟨fun v ↦ by
    have he := fun D ↦ eval_graphAssemblyFormula sigmaOnePairFirstFormula (v 0) D ![] kpair.π₁
      (by definability) (fun x _ y ↦ by simp)
    simp only [Semiformula.Evalb] at he
    simp [sigmaOneWoodinSeedLiftMapFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he, woodinSeedLiftMap]⟩

instance sigmaOneWoodinSeedLiftRow_defined :
    ℒₛₑₜ-function₂[V] (fun j Q ↦ woodinSeedLiftMap (Q ‘ j)) via sigmaOneWoodinSeedLiftRow :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedLiftRow]⟩

instance sigmaOneWoodinSeedProjectionColumnFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun G θ Q ↦ IsOrdinal θ ∧ G = woodinSeedProjectionColumn θ Q)
      via sigmaOneWoodinSeedProjectionColumnFormula :=
  woodinSourceColumnCertificate_defined (fun j Q ↦ (Q ‘ j) ×ˢ ({∅} : V)) sigmaOneWoodinSeedProjectionRow

instance sigmaOneWoodinSeedSectionColumnFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun G θ t ↦ IsOrdinal θ ∧ G = woodinSeedSectionColumn θ t)
      via sigmaOneWoodinSeedSectionColumnFormula :=
  woodinSourceColumnCertificate_defined (fun j t ↦ ({∅} : V) ×ˢ {t ‘ j}) sigmaOneWoodinSeedSectionRow

instance sigmaOneWoodinSeedLiftColumnFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun G θ Q ↦ IsOrdinal θ ∧ G = woodinSeedLiftColumn θ Q)
      via sigmaOneWoodinSeedLiftColumnFormula :=
  woodinSourceColumnCertificate_defined (fun j Q ↦ woodinSeedLiftMap (Q ‘ j)) sigmaOneWoodinSeedLiftRow

end ZFVP
