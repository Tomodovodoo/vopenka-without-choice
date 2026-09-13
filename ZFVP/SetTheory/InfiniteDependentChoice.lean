import ZFVP.SetTheory.PathDependentChoice
import ZFVP.SetTheory.WellOrderedCardinal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternallyFinite (A : V) : Prop := ∃ n ∈ (ω : V), A ≋ n

def IsInternallyInfinite (A : V) : Prop := ¬IsInternallyFinite A

instance isInternallyFinite_definable : ℒₛₑₜ-predicate[V] IsInternallyFinite := by
  unfold IsInternallyFinite
  definability

instance isInternallyInfinite_definable : ℒₛₑₜ-predicate[V] IsInternallyInfinite := by
  unfold IsInternallyInfinite
  definability

theorem injective_finiteSequence_fresh {A s : V} (hA : IsInternallyInfinite A)
    (hs : s ∈ finiteSequences A) (hi : Injective s) : ∃ x ∈ A, x ∉ range s := by
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff _ _).mp hs
  have : IsFunction s := IsFunction.of_mem hsn
  by_contra h
  have hr : range s = A := SetTheory.subset_antisymm (range_subset_of_mem_function hsn) (by
    intro x hx
    by_contra hxr
    exact h ⟨x, hx, hxr⟩)
  have hc := converseGraph_mem_function hsn hi
  rw [hr] at hc
  exact hA ⟨n, hn, ⟨⟨converseGraph s, hc, converseGraph_injective _⟩, ⟨s, hsn, hi⟩⟩⟩

theorem injective_append_fresh {s n x : V} (hs : Injective s) (hx : x ∉ range s) :
    Injective (insert ⟨n, x⟩ₖ s) := by
  intro i j z hi hj
  rcases mem_insert.mp hi with hi | hi <;> rcases mem_insert.mp hj with hj | hj
  · exact (kpair_iff.mp hi).1.trans (kpair_iff.mp hj).1.symm
  · have hzx := (kpair_iff.mp hi).2
    exact False.elim (hx (hzx ▸ mem_range_of_kpair_mem hj))
  · have hzx := (kpair_iff.mp hj).2
    exact False.elim (hx (hzx ▸ mem_range_of_kpair_mem hi))
  · exact hs i j z hi hj

theorem natural_increasing_subset (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hs : ∀ n ∈ (ω : V), F n ⊆ F (succ n)) :
    ∀ m ∈ (ω : V), ∀ n ∈ m, F n ⊆ F m := by
  apply naturalNumber_induction (fun m ↦ ∀ n ∈ m, F n ⊆ F m) (by definability)
  · intro n hn
    simp [zero_def] at hn
  · intro m hm ih n hn
    rcases mem_succ_iff.mp hn with rfl | hn
    · exact hs _ hm
    · exact subset_trans (ih n hn) (hs m hm)

theorem omega_cardLE_of_infinite_dependentChoice (hDC : InternalDependentChoice V)
    {A : V} (hA : IsInternallyInfinite A) : (ω : V) ≤# A := by
  let P : V := {s ∈ finiteSequences A ; Injective s}
  have hP (s : V) : s ∈ P ↔ s ∈ finiteSequences A ∧ Injective s := mem_sep_iff
  let Q : V := {p ∈ P ×ˢ P ; kpair.π₁ p ⊆ kpair.π₂ p ∧
    domain (kpair.π₂ p) = succ (domain (kpair.π₁ p))}
  have hQ (s t : V) : ⟨s, t⟩ₖ ∈ Q ↔ s ∈ P ∧ t ∈ P ∧ s ⊆ t ∧ domain t = succ (domain s) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have he : (∅ : V) ∈ P := (hP _).mpr ⟨empty_mem_finiteSequences A, by
    intro i j z hi _
    exact False.elim (not_mem_empty hi)⟩
  have hserial : ∀ s ∈ P, ∃ t ∈ P, ⟨s, t⟩ₖ ∈ Q := by
    intro s hs
    obtain ⟨hsf, hsi⟩ := (hP s).mp hs
    obtain ⟨x, hx, hxr⟩ := injective_finiteSequence_fresh hA hsf hsi
    let t := insert ⟨domain s, x⟩ₖ s
    have htP : t ∈ P := (hP _).mpr ⟨finiteSequence_append hsf hx, injective_append_fresh hsi hxr⟩
    have ht := function_append_mem ((mem_finiteSequences_iff_domain _ _).mp hsf).2 hx
    exact ⟨t, htP, (hQ s t).mpr ⟨hs, htP, fun p hp ↦ mem_insert.mpr (Or.inr hp),
      domain_eq_of_mem_function ht⟩⟩
  obtain ⟨g, hg, hsteps⟩ := hDC P Q ⟨∅, he⟩ hserial
  have hseq (n : V) (hn : n ∈ (ω : V)) : g ‘ n ∈ finiteSequences A ∧ Injective (g ‘ n) :=
    (hP _).mp (function_value_mem hg hn)
  have htype (n : V) (hn : n ∈ (ω : V)) : g ‘ n ∈ A ^ domain (g ‘ n) :=
    ((mem_finiteSequences_iff_domain _ _).mp (hseq n hn).1).2
  have hdomω (n : V) (hn : n ∈ (ω : V)) : domain (g ‘ n) ∈ (ω : V) :=
    ((mem_finiteSequences_iff_domain _ _).mp (hseq n hn).1).1
  have hext (n : V) (hn : n ∈ (ω : V)) : g ‘ n ⊆ g ‘ (succ n) ∧
      domain (g ‘ (succ n)) = succ (domain (g ‘ n)) := ((hQ _ _).mp (hsteps n hn)).2.2
  have hlen : ∀ n ∈ (ω : V), n ∈ domain (g ‘ (succ n)) := by
    apply naturalNumber_induction (fun n ↦ n ∈ domain (g ‘ (succ n))) (by definability)
    · rw [(hext 0 (by simp)).2]
      exact zero_mem_succ_natural (hdomω 0 (by simp))
    · intro n hn ih
      rw [(hext (succ n) (ω_succ_closed hn)).2]
      exact succ_mem_succ_of_natural_mem (hdomω (succ n) (ω_succ_closed hn)) ih
  let f := definableGraph (ω : V) (fun n ↦ (g ‘ (succ n)) ‘ n) (by definability)
  have hf : f ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦
    function_value_mem (htype (succ n) (ω_succ_closed hn)) (hlen n hn))
  have hval (n : V) (hn : n ∈ (ω : V)) : f ‘ n = (g ‘ (succ n)) ‘ n := value_definableGraph _ _ _ hn
  have hmono := natural_increasing_subset (fun n ↦ g ‘ (succ n)) (by definability)
    (fun n hn ↦ (hext (succ n) (ω_succ_closed hn)).1)
  have hdistinct (n m : V) (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
      (hnm : n ∈ m) : f ‘ n ≠ f ‘ m := by
    intro heq
    have : IsFunction (g ‘ (succ n)) := IsFunction.of_mem (htype (succ n) (ω_succ_closed hn))
    have hp : ⟨n, (g ‘ (succ n)) ‘ n⟩ₖ ∈ g ‘ (succ m) :=
      hmono m hm n hnm _ (kpair_value_mem (hlen n hn))
    have : IsFunction (g ‘ (succ m)) := IsFunction.of_mem (htype (succ m) (ω_succ_closed hm))
    have hp' : ⟨m, (g ‘ (succ m)) ‘ m⟩ₖ ∈ g ‘ (succ m) := kpair_value_mem (hlen m hm)
    have hvals : (g ‘ (succ n)) ‘ n = (g ‘ (succ m)) ‘ m := (hval n hn).symm.trans (heq.trans (hval m hm))
    have hnm' := (hseq (succ m) (ω_succ_closed hm)).2 n m _ (hvals ▸ hp) hp'
    exact mem_irrefl m (hnm' ▸ hnm)
  have : IsFunction f := IsFunction.of_mem hf
  refine ⟨f, hf, ?_⟩
  intro n m z hnz hmz
  have hn : n ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hnz
  have hm : m ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hmz
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have heq := (value_eq_of_kpair_mem hnz).trans (value_eq_of_kpair_mem hmz).symm
  rcases IsOrdinal.mem_trichotomy n m with hlt | he | hgt
  · exact False.elim (hdistinct n m hn hm hlt heq)
  · exact he
  · exact False.elim (hdistinct m n hm hn hgt heq.symm)

theorem not_dependentChoice_of_infinite_no_omega_injection {A : V}
    (hA : IsInternallyInfinite A) (hn : ¬(ω : V) ≤# A) : ¬InternalDependentChoice V :=
  fun hDC ↦ hn (omega_cardLE_of_infinite_dependentChoice hDC hA)

end ZFVP
