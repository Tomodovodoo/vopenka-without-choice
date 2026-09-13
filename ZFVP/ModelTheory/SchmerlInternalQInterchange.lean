import ZFVP.ModelTheory.SchmerlInternalSwap
import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms

/-! Internal Q interchange. The second formula is constructed by swapping
the first two binders. Every witness fiber and the projection used by the
countable-union argument are actual internal sets. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The consequent is existential-Q or Q-existential, expressed as
implication from the negation of its first disjunct. -/
noncomputable def qInterchangeCode (φ ψ : V) : V :=
  impCode (qCode (exsCode φ)) (impCode (negCode (exsCode (qCode ψ))) (qCode (exsCode ψ)))

instance qInterchangeCode_definable : ℒₛₑₜ-function₂[V] qInterchangeCode := by
  unfold qInterchangeCode
  definability

theorem holds_qInterchangeCode {L F H M n φ b : V}
    (hF : IsFragment L F) (hH : IsFragment L H) (hM : IsStructureCode L M)
    (hAC : InternalChoice V) (hφ : ⟨succ (succ n), φ⟩ₖ ∈ F)
    (ht : ⟨n, qInterchangeCode φ (swapCode L F n φ)⟩ₖ ∈ H)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L H M n (qInterchangeCode φ (swapCode L F n φ)) b := by
  have hn := (hH.node ht).1
  have hl := hH.imp_left_mem ht
  have hr := hH.imp_right_mem ht
  have hleft := hH.q_mem hl
  have hφH := hH.exs_mem hleft
  have hexQ := hH.neg_mem (hH.imp_left_mem hr)
  have hQ := hH.exs_mem hexQ
  have hψH := hH.q_mem hQ
  have hQex := hH.imp_right_mem hr
  have hex := hH.q_mem hQex
  let R : V → V → Prop := fun x y ↦ Holds L H M (succ (succ n)) φ
    (assignmentPrepend (succ n) (assignmentPrepend n b y) x)
  have hR : ℒₛₑₜ-relation R := by unfold R Holds; definability
  let := hR
  have hswap (x y : V) (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
      Holds L H M (succ (succ n)) (swapCode L F n φ)
        (assignmentPrepend (succ n) (assignmentPrepend n b x) y) ↔ R x y :=
    (holds_swapCode_in_fragment hF hH hM hn hφ hψH hb hx hy).trans
      (holds_fragment_iff hF hH _ _ hφ hφH _)
  have hleftFiber : witnessFiber M n b (truthGraph L H M) (exsCode φ) =
      {y ∈ structureDomain M ; ∃ x ∈ structureDomain M, R x y} := by
    apply mem_ext
    intro y
    simp only [witnessFiber, mem_sep_iff]
    apply and_congr_right
    intro hy
    exact holds_exs hH hleft (assignmentPrepend_mem_function hn hb hy)
  have hrowFiber (x : V) (hx : x ∈ structureDomain M) :
      witnessFiber M (succ n) (assignmentPrepend n b x) (truthGraph L H M) (swapCode L F n φ) =
        sep (structureDomain M) (fun y ↦ R x y) (by unfold R Holds; definability) := by
    apply mem_ext
    intro y
    simp only [witnessFiber, mem_sep_iff]
    apply and_congr_right
    intro hy
    exact hswap x y hx hy
  have hrightFiber : witnessFiber M n b (truthGraph L H M) (exsCode (swapCode L F n φ)) =
      sep (structureDomain M) (fun x ↦ ∃ y ∈ structureDomain M, R x y)
        (by unfold R Holds; definability) := by
    apply mem_ext
    intro x
    simp only [witnessFiber, mem_sep_iff]
    apply and_congr_right
    intro hx
    change Holds L H M (succ n) (exsCode (swapCode L F n φ)) (assignmentPrepend n b x) ↔ _
    rw [holds_exs hH hex (assignmentPrepend_mem_function hn hb hx)]
    apply exists_congr
    intro y
    exact and_congr_right (fun hy ↦ hswap x y hx hy)
  rw [qInterchangeCode, holds_imp hH ht hb, holds_q hH hl hb, hleftFiber,
    holds_imp hH hr hb, holds_neg hH (hH.imp_left_mem hr) hb,
    holds_q hH hQex hb, hrightFiber]
  intro hbig hnot
  rcases internal_uncountable_interchange hAC (structureDomain M) R hR hbig with hrow | hmany
  · obtain ⟨x, hx, hrow⟩ := hrow
    exact False.elim (hnot ((holds_exs hH hexQ hb).mpr ⟨x, hx,
      (holds_q hH hQ (assignmentPrepend_mem_function hn hb hx)).mpr (by
        simpa only [hrowFiber x hx] using hrow)⟩))
  · exact hmany

/-- A source fragment witnesses the actual syntactic binder swap. This
predicate contains no semantic condition or assumed soundness premise. -/
def IsQInterchangeAxiom (L n χ : V) : Prop := ∃ F φ ψ,
  IsFragment L F ∧ ⟨succ (succ n), φ⟩ₖ ∈ F ∧
    ψ = swapCode L F n φ ∧ χ = qInterchangeCode φ ψ

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

instance isQInterchangeAxiom_definable : ℒₛₑₜ-relation₃[V] IsQInterchangeAxiom := by
  unfold IsQInterchangeAxiom
  definability

theorem IsQInterchangeAxiom.sound {L H M n χ b : V} (hχ : IsQInterchangeAxiom L n χ)
    (hH : IsFragment L H) (hM : IsStructureCode L M) (hAC : InternalChoice V)
    (ht : ⟨n, χ⟩ₖ ∈ H) (hb : b ∈ structureDomain M ^ n) : Holds L H M n χ b := by
  obtain ⟨F, φ, ψ, hF, hφ, rfl, rfl⟩ := hχ
  exact holds_qInterchangeCode hF hH hM hAC hφ ht hb

end ZFVP.Infinitary.Internal
