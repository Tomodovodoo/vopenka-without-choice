import ZFVP.ModelTheory.SchmerlCodedSourceForcing
import ZFVP.ModelTheory.SchmerlCodedFunctionFamilyTransport
import ZFVP.ModelTheory.SchmerlInternalSimultaneousSpecialization

/-! One forcing extension supplies the class coloring and every finite-function
coloring, preserving all relevant cofinal branches at once. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def adjoinTreeFamily (I a t f : V) : V := by
  classical
  exact definableGraph (insert a I) (fun s ↦ if s = a then t else f ‘ s) (by
    have h : ℒₛₑₜ-relation[V] (fun y s ↦ (s = a ∧ y = t) ∨ (s ≠ a ∧ y = f ‘ s)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = (if v 1 = a then t else f ‘ (v 1)) ↔ _
    by_cases he : v 1 = a <;> simp [he])

instance adjoinTreeFamily_isFunction (I a t f : V) : IsFunction (adjoinTreeFamily I a t f) :=
  inferInstanceAs (IsFunction (definableGraph _ _ _))

theorem domain_adjoinTreeFamily (I a t f : V) : domain (adjoinTreeFamily I a t f) = insert a I :=
  domain_definableGraph _ _ _

theorem adjoinTreeFamily_value_root (I a t f : V) : (adjoinTreeFamily I a t f) ‘ a = t := by
  classical
  rw [adjoinTreeFamily, value_definableGraph _ _ _ (by simp)]
  simp

theorem adjoinTreeFamily_value_old {I a t f s : V} (hs : s ∈ I) (ha : a ∉ I) :
    (adjoinTreeFamily I a t f) ‘ s = f ‘ s := by
  classical
  rw [adjoinTreeFamily, value_definableGraph _ _ _ (mem_insert.mpr (Or.inr hs))]
  exact ite_eq_right (fun he : s = a ↦ ha (he ▸ hs))

structure CodedSourceSpecialization (M c C : V) (F : ForcingContext V) (f g : F.Model) : Prop where
  choice : InternalChoice F.Model
  hartogs : F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model)
  class_color : f ∈ (ω : F.Model) ^ F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c)
  class_weak : InternallyWeakSpecialization
    (F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c))
    (F.check (codedSelectedClassOrder M (hartogsNumber (ω : V)) c)) f
  function_colors : ∀ s ∈ codedInfiniteSets M,
    g ‘ (F.check s) ∈ (ω : F.Model) ^ F.check (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) (C ‘ s)) ∧
      InternallyWeakSpecialization
        (F.check (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) (C ‘ s)))
        (F.check (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) (C ‘ s))) (g ‘ (F.check s))
  class_branches : ∀ B : F.Model,
    IsInternalCofinalBranch
      (F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c))
      (F.check (codedSelectedClassOrder M (hartogsNumber (ω : V)) c))
      (F.check (hartogsNumber (ω : V)))
      (F.check (codedSelectedClassRank M (hartogsNumber (ω : V)) c)) B →
    ∃ A : V, IsInternalCofinalBranch
      (codedSelectedClassNodes M (hartogsNumber (ω : V)) c)
      (codedSelectedClassOrder M (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
      (codedSelectedClassRank M (hartogsNumber (ω : V)) c) A ∧ F.check A = B
  function_branches : ∀ s ∈ codedInfiniteSets M, ∀ B : F.Model,
    IsInternalCofinalBranch
      (F.check (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) (C ‘ s)))
      (F.check (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) (C ‘ s)))
      (F.check (hartogsNumber (ω : V)))
      (F.check (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) (C ‘ s))) B →
    ∃ A : V, IsInternalCofinalBranch
      (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) (C ‘ s))
      (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) (C ‘ s)) (hartogsNumber (ω : V))
      (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) (C ‘ s)) A ∧ F.check A = B

theorem IsCodedRubinFinSmallSource.exists_simultaneous_specialization [Countable V]
    (hAC : InternalChoice V) {M : V} (h : IsCodedRubinFinSmallSource M) :
    ∃ c C, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedOrdinals M) (codedOrdinalOrder M) c ∧
      IsCodedFiniteDomainFamily M (hartogsNumber (ω : V)) C ∧
      ∃ F : ForcingContext V, ∃ f g : F.Model, CodedSourceSpecialization M c C F f g := by
  obtain ⟨C, hC⟩ := h.exists_finiteDomainFamily hAC
  have hfamily := h.functionFamily_data hAC hC
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, hcard, hRubin, _⟩ := h
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  have hcode : R.code = binaryRelationStructureCode D E := rfl
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  let κ := hartogsNumber (ω : V)
  let I := codedInfiniteSets R.code
  have hDI : D ∉ I := by
    intro hDmem
    apply mem_irrefl D
    simpa only [hcode, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code D hDmem
  obtain ⟨c, hc⟩ := R.exists_cofinal_ordinal_chain hRubin
  let T := adjoinTreeFamily I D (codedSelectedClassNodes R.code κ c) (codedFunctionTreeFamily R.code κ C)
  let S := adjoinTreeFamily I D (codedSelectedClassOrder R.code κ c) (codedFunctionOrderFamily R.code κ C)
  let r := adjoinTreeFamily I D (codedSelectedClassRank R.code κ c) (codedFunctionRankFamily R.code κ C)
  have hJ : insert D I ≤# κ := by
    have hh : insert D I ≤# succ κ := cardLE_insert_fresh hfamily.1 hDI (mem_irrefl κ)
    exact hh.trans (succ_cardLE_of_omega_subset (IsOrdinal.toIsTransitive.transitive _ omega_mem_hartogs_omega))
  have hT : ∀ s ∈ insert D I, InternalRankedTree (T ‘ s) (S ‘ s) κ (r ‘ s) := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · simpa only [T, S, r, adjoinTreeFamily_value_root] using R.selectedClassTree hc
    · simpa only [T, S, r, adjoinTreeFamily_value_old hs hDI, hcode, κ] using (hfamily.2 s hs).1
  have hS : ∀ s ∈ insert D I, IsForcingPoset (T ‘ s) (S ‘ s) := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · simpa only [T, S, adjoinTreeFamily_value_root] using R.selectedClassOrder_poset κ c
    · simpa only [T, S, adjoinTreeFamily_value_old hs hDI, hcode, κ] using (hfamily.2 s hs).2.1
  have hinj : ∀ s ∈ insert D I, ∀ x ∈ T ‘ s, ∀ y ∈ T ‘ s,
      ⟨x, y⟩ₖ ∈ S ‘ s → (r ‘ s) ‘ x = (r ‘ s) ‘ y → x = y := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · simp only [T, S, r, adjoinTreeFamily_value_root]
      exact fun _ hx _ hy hxy he ↦ R.selectedClassRank_comparable_injective hc hx hy hxy he
    · simpa only [T, S, r, adjoinTreeFamily_value_old hs hDI, hcode, κ] using (hfamily.2 s hs).2.2.1
  have hbranches : ∀ s ∈ insert D I, internalCofinalBranches (T ‘ s) (S ‘ s) κ (r ‘ s) ≤# κ := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · simpa only [T, S, r, adjoinTreeFamily_value_root] using R.selectedBranches_cardLE hAC hc hRubin hcard
    · simpa only [T, S, r, adjoinTreeFamily_value_old hs hDI, hcode, κ] using (hfamily.2 s hs).2.2.2
  have hdT : insert D I ⊆ domain T := by rw [domain_adjoinTreeFamily]
  have hdS : insert D I ⊆ domain S := by rw [domain_adjoinTreeFamily]
  have hdr : insert D I ⊆ domain r := by rw [domain_adjoinTreeFamily]
  obtain ⟨F, hACF, hκ, ⟨g, _, _, hg⟩, hpres⟩ :=
    exists_internal_simultaneous_weak_specialization_extension hAC hdT hdS hdr hJ hT hS hinj hbranches
  have hDc : F.check D ∈ F.check (insert D I) := (F.check_mem_iff _ _).mpr (by simp)
  have hclass := hg (F.check D) hDc
  rw [F.check_value (hdT D (by simp)), F.check_value (hdS D (by simp))] at hclass
  simp only [T, S, adjoinTreeFamily_value_root] at hclass
  rw [← hcode]
  refine ⟨c, C, hc, hC, F, g ‘ (F.check D), g,
    ⟨hACF, hκ, hclass.1, hclass.2, ?_, ?_, ?_⟩⟩
  · intro s hs
    have hsI : s ∈ I := hs
    have hsJ : s ∈ insert D I := mem_insert.mpr (Or.inr hs)
    have hh := hg (F.check s) ((F.check_mem_iff _ _).mpr hsJ)
    rw [F.check_value (hdT s hsJ), F.check_value (hdS s hsJ)] at hh
    simpa only [T, S, adjoinTreeFamily_value_old hsI hDI,
      value_codedFunctionTreeFamily hs, value_codedFunctionOrderFamily hs] using hh
  · intro B hB
    have hh := hpres D (by simp) B
    simp only [T, S, r, adjoinTreeFamily_value_root] at hh
    apply hh
    simpa only [hκ] using hB
  · intro s hs B hB
    have hsI : s ∈ I := hs
    have hh := hpres s (mem_insert.mpr (Or.inr hs)) B
    simp only [T, S, r, adjoinTreeFamily_value_old hsI hDI,
      value_codedFunctionTreeFamily hs, value_codedFunctionOrderFamily hs,
      value_codedFunctionRankFamily hs] at hh
    apply hh
    simpa only [hκ] using hB

end ZFVP.Schmerl
