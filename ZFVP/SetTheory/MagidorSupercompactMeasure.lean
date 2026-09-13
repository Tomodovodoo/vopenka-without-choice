import ZFVP.SetTheory.MagidorWitnessMeasures
import ZFVP.SetTheory.NormalFineMeasureStage
import ZFVP.SetTheory.ClosedRankStages
import ZFVP.SetTheory.PiOneVopenkaMagidorUnconditional
import ZFVP.SetTheory.MagidorVopenkaForward

/-! # From small embeddings to normal fine measures

Magidor's theorem (Magidor 1971; Kanamori, *The Higher Infinite*, 22.10) says that `κ` is
supercompact iff every rank above `κ` is the target of a small elementary embedding whose
critical point is sent to `κ`. This module proves the direction from embeddings to measures:
`IsMagidorSupercompact κ → IsSupercompact κ`, where `IsSupercompact` is the measure definition
of `ZFVP.SetTheory.SupercompactMeasure`, the one Bagaria and the paper use.

The argument uses no choice and no ultrapower. Given `lam`, pick a successor-closed `gam` above
`lam` and `ω`, take a Magidor witness `e : V_lb → V_gam` with critical point `ab` sent to `κ`,
and read `magidorWitness_measures` off it: `ab` is an initial ordinal above `ω` carrying a
normal fine measure on `P_ab(ξ)` for every `ξ ∈ lb`. That is exactly what
`supercompactStageFormula` says about `ab` inside `V_lb`, so elementarity moves it to `κ` inside
`V_gam`, and `eval_supercompactStageFormula` reads it back there.

The converse direction, measures to small embeddings, is not formalized: it needs the ultrapower
of a rank stage by a normal fine measure and the closure of the target under `lam`-sequences.
That is why the last theorem below carries `hstrengthen` as a hypothesis. `hstrengthen` is the
step from a proper class of measure-supercompact cardinals to a proper class of Magidor
witnesses with a prescribed high critical point and a `C(n+1)` source stage, the predicate
`IsCorrectHighCriticalMagidorSupercompact` of `ZFVP.SetTheory.MagidorVopenkaForward`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- One instance of Magidor's theorem in the direction from embeddings to measures: at a single
ordinal `lam` above `κ`, a small embedding into a successor-closed rank above `lam` gives a
normal fine measure on `P_κ(lam)`, and gives that `κ` is an initial ordinal above `ω`. -/
theorem IsMagidorSupercompact.normalFineMeasure {κ lam : V} (h : IsMagidorSupercompact κ)
    (hlam : IsOrdinal lam) (hsub : κ ⊆ lam) :
    IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧ ∃ U, IsNormalFineMeasure κ lam U := by
  have hκo : IsOrdinal κ := h.1
  let := hκo
  let := hlam
  let := union_isOrdinal lam (ω : V)
  obtain ⟨gam, hgamo, hsβ, hgamsucc, -⟩ := exists_closed_limit_ordinal (succ (lam ∪ (ω : V)))
  let := hgamo
  -- `lam`, `ω` and `κ` all sit below the successor-closed `gam`
  have hβgam : ∀ x : V, IsOrdinal x → x ⊆ lam ∪ (ω : V) → x ∈ gam := by
    intro x hx hxs
    let := hx
    exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_of_subset hxs) hsβ
  have hlamgam : lam ∈ gam :=
    hβgam lam hlam (fun y hy ↦ mem_union_iff.mpr (Or.inl hy))
  have hωgam : (ω : V) ∈ gam :=
    hβgam (ω : V) inferInstance (fun y hy ↦ mem_union_iff.mpr (Or.inr hy))
  have hκgam : κ ∈ gam :=
    hβgam κ hκo (fun y hy ↦ mem_union_iff.mpr (Or.inl (hsub y hy)))
  -- a Magidor witness at `gam`
  obtain ⟨lb, hlbκ, ab, hablb, e, he, hc, hek⟩ := h.2 gam hgamo hκgam
  have hlbo : IsOrdinal lb := IsOrdinal.of_mem hlbκ
  let := hlbo
  let := hc.ordinal
  obtain ⟨hlbsucc, habinit, hωab, hmeas⟩ :=
    magidorWitness_measures hgamsucc he hc hek hlbκ
  have hωlb : (ω : V) ∈ lb := omega_mem_of_criticalPoint hlbsucc he hc
  have habH : ab ∈ hierarchy lb := hc.mem_domain
  -- the sentence "a is supercompact in the measure sense" holds at `ab` inside `V_lb`
  have hsrc : supercompactStageFormula.Evalb
      (![⟨ab, habH⟩] : Fin 1 → SetDomain (hierarchy lb)) := by
    refine (eval_supercompactStageFormula hlbsucc hωlb habH).mpr ⟨habinit, hωab, ?_⟩
    intro ξ hξ _
    obtain ⟨U, -, hU⟩ := hmeas ξ hξ
    exact ⟨U, hU⟩
  -- move it along `e`, which sends `ab` to `κ`
  have hκH : κ ∈ hierarchy gam := ordinal_mem_hierarchy_iff.mpr hκgam
  have htgt := (he.eval_semisentence supercompactStageFormula ![⟨ab, habH⟩]).mp hsrc
  have hfun : he.toFunction ∘ (![⟨ab, habH⟩] : Fin 1 → SetDomain (hierarchy lb))
      = (![⟨κ, hκH⟩] : Fin 1 → SetDomain (hierarchy gam)) := by
    funext i
    refine Fin.cases ?_ (fun t ↦ Fin.elim0 t) i
    exact Subtype.ext hek
  rw [hfun] at htgt
  -- and read it back at `κ` inside `V_gam`
  obtain ⟨hκinit, hωκ, hall⟩ := (eval_supercompactStageFormula hgamsucc hωgam hκH).mp htgt
  exact ⟨hκinit, hωκ, hall lam hlamgam hsub⟩

/-- Magidor's theorem, the direction from small embeddings to measures: a cardinal with a small
elementary embedding into every rank above it is supercompact in the measure sense. -/
theorem IsMagidorSupercompact.isSupercompact {κ : V} (h : IsMagidorSupercompact κ) :
    IsSupercompact κ := by
  obtain ⟨hinit, hω, -⟩ := h.normalFineMeasure h.1 (fun x hx ↦ hx)
  exact ⟨hinit, hω, fun lam hlam hsub ↦ (h.normalFineMeasure hlam hsub).2.2⟩

/-- The Pi(1) fragment of Vopenka's principle gives a proper class of supercompact cardinals in
the measure sense, with internal choice the only extra hypothesis. -/
theorem supercompact_unbounded_of_pi_one_vopenka (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ := by
  intro α hα
  obtain ⟨κ, hακ, hκ⟩ := magidorSupercompact_unbounded_of_pi_one_vopenka hAC hVP α hα
  exact ⟨κ, hακ, hκ.isSupercompact⟩

/-- Bagaria's Theorem 4.3(2) at `n = 1` with supercompactness read in the measure sense,
carrying the one remaining step as a hypothesis: a proper class of supercompact cardinals gives
a proper class of Magidor witnesses with a critical point above a prescribed ordinal and a
`C(n+1)` source stage. -/
theorem pi_one_vopenka_iff_unbounded_supercompact (hAC : InternalChoice V)
    (hstrengthen : (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ) →
      ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
        IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound κ) :
    (∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) ↔
      (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ) := by
  constructor
  · intro hVP
    exact supercompact_unbounded_of_pi_one_vopenka hAC hVP
  · intro hSC
    exact magidorSupercompact_unbounded_implies_pi_one_vopenka (hstrengthen hSC)

end ZFVP
