import ZFVP.SetTheory.FiniteRealMapMinimum
import ZFVP.SetTheory.FiniteRangeFibers
import ZFVP.SetTheory.FiniteDomainEnumerationFamily
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.FiniteSequences

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableFunction₄.comp

noncomputable def finiteFiberLabels (H x : V) : V :=
  {j ∈ domain H ; IsNonempty (exactSupportFiber H j x)}

instance finiteFiberLabels_definable : ℒₛₑₜ-function₂[V] finiteFiberLabels := by
  have h : ℒₛₑₜ-relation₃[V] (fun L H x ↦ ∀ j, j ∈ L ↔
      j ∈ domain H ∧ IsNonempty (exactSupportFiber H j x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [finiteFiberLabels, mem_sep_iff]
  rfl

noncomputable def finiteFiberLabel (H f x : V) : V := wellOrderSelection f (finiteFiberLabels H x)

instance finiteFiberLabel_definable : ℒₛₑₜ-function₃[V] finiteFiberLabel := by
  unfold finiteFiberLabel
  definability

noncomputable def finiteFiberAssignment (H f e x : V) : V :=
  finiteRealMapMinimum (range (e ‘ (finiteFiberLabel H f x)))
    (exactSupportFiber H (finiteFiberLabel H f x) x)

instance finiteFiberAssignment_definable : ℒₛₑₜ-function₄[V] finiteFiberAssignment := by
  change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦
    finiteRealMapMinimum (range ((v 2) ‘ (finiteFiberLabel (v 0) (v 1) (v 3))))
      (exactSupportFiber (v 0) (finiteFiberLabel (v 0) (v 1) (v 3)) (v 3)))
  have hj : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦ finiteFiberLabel (v 0) (v 1) (v 3)) :=
    Language.DefinableFunction₃.comp (F := finiteFiberLabel) (by definability) (by definability) (by definability)
  have hev : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦ (v 2) ‘ (finiteFiberLabel (v 0) (v 1) (v 3))) :=
    Language.DefinableFunction₂.comp (F := value) (by definability) hj
  exact Language.DefinableFunction₂.comp (F := finiteRealMapMinimum)
    (Language.DefinableFunction₁.comp (F := range) hev)
    (Language.DefinableFunction₃.comp (F := exactSupportFiber) (by definability) hj (by definability))
noncomputable def finiteFiberCode (H f e x : V) : V :=
  ⟨f ‘ (finiteFiberLabel H f x), compose (e ‘ (finiteFiberLabel H f x)) (finiteFiberAssignment H f e x)⟩ₖ

instance finiteFiberCode_definable : ℒₛₑₜ-function₄[V] finiteFiberCode := by
  change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦
    ⟨(v 1) ‘ (finiteFiberLabel (v 0) (v 1) (v 3)),
      compose ((v 2) ‘ (finiteFiberLabel (v 0) (v 1) (v 3)))
        (finiteFiberAssignment (v 0) (v 1) (v 2) (v 3))⟩ₖ)
  have hj : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦ finiteFiberLabel (v 0) (v 1) (v 3)) :=
    Language.DefinableFunction₃.comp (F := finiteFiberLabel) (by definability) (by definability) (by definability)
  have hfv : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦ (v 1) ‘ (finiteFiberLabel (v 0) (v 1) (v 3))) :=
    Language.DefinableFunction₂.comp (F := value) (by definability) hj
  have hev : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦ (v 2) ‘ (finiteFiberLabel (v 0) (v 1) (v 3))) :=
    Language.DefinableFunction₂.comp (F := value) (by definability) hj
  exact Language.DefinableFunction₂.comp (F := kpair) hfv
    (Language.DefinableFunction₂.comp (F := compose) hev finiteFiberAssignment_definable)
/-- Select an ordinal label and an assignment in its finite fiber, then enumerate the
assignment as a finite sequence. The resulting graph is constructed internally. -/
theorem finiteFiber_cardLE_ordinal_prod_sequences {X R H f e α : V}
    (hα : IsOrdinal α) (hf : f ∈ α ^ domain H) (hfi : Injective f)
    (hR : R ⊆ ℘ (ω : V))
    (hH : ∀ j ∈ domain H, IsFunction (H ‘ j))
    (hne : ∀ x ∈ X, ∃ j ∈ domain H, IsNonempty (exactSupportFiber H j x))
    (hfinite : ∀ x ∈ X, ∀ j ∈ domain H, IsInternallyFinite (exactSupportFiber H j x))
    (he : ∀ j ∈ domain H, ∃ n ∈ (ω : V),
      e ‘ j ∈ (range (e ‘ j)) ^ n ∧ range (e ‘ j) ⊆ (ω : V) ∧
      ∀ a ∈ domain (H ‘ j), a ∈ R ^ (range (e ‘ j))) :
    X ≤# α ×ˢ finiteSequences R := by
  have : IsOrdinal α := hα
  have hlabel (x : V) (hx : x ∈ X) :
      finiteFiberLabel H f x ∈ domain H ∧
      IsNonempty (exactSupportFiber H (finiteFiberLabel H f x) x) := by
    obtain ⟨j, hj, hjn⟩ := hne x hx
    exact mem_sep_iff.mp (wellOrderSelection_mem hf hfi
      (fun _ hz ↦ (mem_sep_iff.mp hz).1)
      ⟨j, mem_sep_iff.mpr ⟨hj, hjn⟩⟩)
  have hchoice (x : V) (hx : x ∈ X) :
      finiteFiberAssignment H f e x ∈ exactSupportFiber H (finiteFiberLabel H f x) x := by
    obtain ⟨hj, hjn⟩ := hlabel x hx
    obtain ⟨n, _, _, hB, hmaps⟩ := he _ hj
    apply finiteRealMapMinimum_mem hB (hfinite x hx _ hj) hjn
    intro a ha
    exact mem_function_of_mem_function_of_subset
      (hmaps a ((mem_exactSupportFiber _ _ _ _).mp ha).1) hR
  have hcode (x : V) (hx : x ∈ X) : finiteFiberCode H f e x ∈ α ×ˢ finiteSequences R := by
    obtain ⟨hj, _⟩ := hlabel x hx
    obtain ⟨n, hn, hen, _, hmaps⟩ := he _ hj
    have ha := hmaps _ ((mem_exactSupportFiber _ _ _ _).mp (hchoice x hx)).1
    exact kpair_mem_iff.mpr ⟨function_value_mem hf hj,
      (mem_finiteSequences_iff R _).mpr ⟨n, hn, compose_function hen ha⟩⟩
  refine ⟨definableGraph X (finiteFiberCode H f e) (by definability),
    definableGraph_mem_function_of_mapsTo _ _ _ _ hcode, ?_⟩
  intro x y z hx hy
  obtain ⟨hxX, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hx
  obtain ⟨hyX, hcodes⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hy
  obtain ⟨hlabels, hseq⟩ := kpair_iff.mp hcodes
  have hjx := (hlabel x hxX).1
  have hjy := (hlabel y hyX).1
  have hj : finiteFiberLabel H f x = finiteFiberLabel H f y :=
    injective_value_eq hf hfi hjx hjy hlabels
  have hcX := (mem_exactSupportFiber _ _ _ _).mp (hchoice x hxX)
  have hcY := (mem_exactSupportFiber _ _ _ _).mp (hchoice y hyX)
  obtain ⟨n, _, hen, _, hmaps⟩ := he _ hjx
  have haX := hmaps _ hcX.1
  have haY := hmaps _ (hj.symm ▸ hcY.1)
  have hseq' : compose (e ‘ (finiteFiberLabel H f x)) (finiteFiberAssignment H f e x) =
      compose (e ‘ (finiteFiberLabel H f x)) (finiteFiberAssignment H f e y) := by
    simpa only [← hj] using hseq
  have ha := compose_cancel_surjective hen rfl haX haY hseq'
  have : IsFunction (H ‘ (finiteFiberLabel H f x)) := hH _ hjx
  exact IsFunction.unique hcX.2.1 (ha.symm ▸ (hj.symm ▸ hcY.2.1))

end ZFVP

