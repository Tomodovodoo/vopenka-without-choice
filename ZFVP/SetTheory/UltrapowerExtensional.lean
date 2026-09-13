import ZFVP.SetTheory.UltrapowerBase
import ZFVP.SetTheory.InternalChoice

/-! Extensionality for the internal ultrapower. If two functions from the index set into a
transitive set have the same almost everywhere members among all such functions, then they are
almost everywhere equal. This is the layer that makes the Mostowski collapse of the almost
everywhere membership relation identify exactly the almost everywhere equal functions, and it is
the point where internal choice is used: a witness separating the two values has to be picked at
every index where they differ. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- At the index `p`, the members of `A` that separate the value of `f` from the value of `g`,
together with the fallback point `a` at the indices where the two values agree. The fallback keeps
the family nonempty at every index, so a single choice function covers the whole index set. -/
noncomputable def differenceWitnesses (A a f g p : V) : V :=
  {z ∈ A ; (z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨ (f ‘ p = g ‘ p ∧ z = a)}

theorem mem_differenceWitnesses_iff (A a f g p z : V) :
    z ∈ differenceWitnesses A a f g p ↔
      z ∈ A ∧ ((z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨ (f ‘ p = g ‘ p ∧ z = a)) :=
  mem_sep_iff

theorem differenceWitnesses_definable_one (A a f g : V) :
    ℒₛₑₜ-function₁[V] (differenceWitnesses A a f g) := by
  have h : ℒₛₑₜ-relation[V] (fun S p ↦ ∀ z, z ∈ S ↔
      z ∈ A ∧ ((z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨
        (f ‘ p = g ‘ p ∧ z = a))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = differenceWitnesses A a f g (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [differenceWitnesses, mem_sep_iff]

theorem differenceWitnesses_subset (A a f g p : V) : differenceWitnesses A a f g p ⊆ A := by
  intro z hz
  exact ((mem_differenceWitnesses_iff A a f g p z).mp hz).1

/-- The family of separating witnesses is nonempty at every index. -/
theorem differenceWitnesses_nonempty {P A a f g : V} [IsTransitive A] (ha : a ∈ A)
    (hf : f ∈ A ^ P) (hg : g ∈ A ^ P) {p : V} (hp : p ∈ P) :
    IsNonempty (differenceWitnesses A a f g p) := by
  by_cases heq : f ‘ p = g ‘ p
  · exact ⟨⟨a, (mem_differenceWitnesses_iff A a f g p a).mpr ⟨ha, Or.inr (Or.inr ⟨heq, rfl⟩)⟩⟩⟩
  · have hex : ∃ z, ¬(z ∈ f ‘ p ↔ z ∈ g ‘ p) := by
      by_contra hc
      exact heq (mem_ext fun z ↦ not_not.mp (fun hz ↦ hc ⟨z, hz⟩))
    obtain ⟨z, hz⟩ := hex
    by_cases hzf : z ∈ f ‘ p
    · have hzg : z ∉ g ‘ p := fun hzg ↦ hz ⟨fun _ ↦ hzg, fun _ ↦ hzf⟩
      have hzA : z ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hzf (function_value_mem hf hp)
      exact ⟨⟨z, (mem_differenceWitnesses_iff A a f g p z).mpr ⟨hzA, Or.inl ⟨hzf, hzg⟩⟩⟩⟩
    · have hzg : z ∈ g ‘ p := by
        by_contra hc
        exact hz ⟨fun hh ↦ absurd hh hzf, fun hh ↦ absurd hh hc⟩
      have hzA : z ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hzg (function_value_mem hg hp)
      exact ⟨⟨z, (mem_differenceWitnesses_iff A a f g p z).mpr ⟨hzA, Or.inr (Or.inl ⟨hzg, hzf⟩)⟩⟩⟩

/-- A function whose domain is `P` and whose values lie in `A` is a member of `A ^ P`. -/
theorem mem_function_of_values {P A k : V} (hk : IsFunction k) (hd : domain k = P)
    (hval : ∀ p ∈ P, k ‘ p ∈ A) : k ∈ A ^ P := by
  have : IsFunction k := hk
  obtain ⟨X', Y', hk'⟩ := hk.mem_func
  rw [mem_function_iff]
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨x, -, y, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hk' q hq)
    have hx : x ∈ P := hd ▸ mem_domain_of_kpair_mem hq
    have hy : y = k ‘ x := (value_eq_of_kpair_mem hq).symm
    exact kpair_mem_iff.mpr ⟨hx, hy ▸ hval x hx⟩
  · intro x hx
    rw [← hd] at hx
    exact ⟨k ‘ x, kpair_value_mem hx, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩

/-- Two functions into a transitive set with the same a.e. members are a.e. equal. This is
extensionality for the ultrapower, and it is where internal choice enters: a witness has to be
picked at every index where the two values differ. -/
theorem aeEq_of_aeMem_iff (hAC : InternalChoice V) {P U A f g : V} [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hA : IsNonempty A) (hf : f ∈ A ^ P) (hg : g ∈ A ^ P)
    (h : ∀ k, k ∈ A ^ P → (AEMem P U k f ↔ AEMem P U k g)) :
    AEEq P U f g := by
  by_contra hnot
  have hD : relativeComplement P (agreementSet P f g) ∈ U :=
    (hU.compl_mem_iff (agreementSet_subset P f g)).mpr hnot
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨k, hkfun, hkdom, hkval⟩ :=
    choice_for_definable_family hAC P (differenceWitnesses A a f g)
      (differenceWitnesses_definable_one A a f g)
      (fun p hp ↦ differenceWitnesses_nonempty ha hf hg hp)
  have hkA : k ∈ A ^ P :=
    mem_function_of_values hkfun hkdom
      (fun p hp ↦ differenceWitnesses_subset A a f g p _ (hkval p hp))
  -- On the complement of the agreement set the two values differ, so the chosen witness lies in
  -- exactly one of them.
  have hsplit : ∀ p ∈ relativeComplement P (agreementSet P f g),
      p ∈ P ∧ ((k ‘ p ∈ f ‘ p ∧ k ‘ p ∉ g ‘ p) ∨ (k ‘ p ∈ g ‘ p ∧ k ‘ p ∉ f ‘ p)) := by
    intro p hp
    rw [mem_relativeComplement_iff] at hp
    obtain ⟨hpP, hpa⟩ := hp
    have hne : f ‘ p ≠ g ‘ p := fun he ↦ hpa ((mem_agreementSet_iff P f g p).mpr ⟨hpP, he⟩)
    have hw := (mem_differenceWitnesses_iff A a f g p _).mp (hkval p hpP)
    refine ⟨hpP, ?_⟩
    rcases hw.2 with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd h3.1 hne
  set D₁ : V := membershipSet (relativeComplement P (agreementSet P f g)) k f with hD₁
  have hD₁sub : D₁ ⊆ relativeComplement P (agreementSet P f g) :=
    membershipSet_subset _ k f
  have hD₁P : D₁ ⊆ P := fun p hp ↦ (hsplit p (hD₁sub p hp)).1
  rcases hU.dichotomy' hD₁P with hin | hout
  · -- The witness is a.e. in `f`, hence a.e. in `g`, but it is nowhere in `g` on `D₁`.
    have hmemf : AEMem P U k f := by
      refine hU.mem_of_subset hin ?_ (membershipSet_subset P k f)
      intro p hp
      have hp' := (mem_membershipSet_iff _ k f p).mp hp
      exact (mem_membershipSet_iff P k f p).mpr ⟨(hsplit p hp'.1).1, hp'.2⟩
    have hmemg : AEMem P U k g := (h k hkA).mp hmemf
    obtain ⟨p, hp⟩ := (hU.isNonempty_of_mem (hU.inter_mem hin hmemg)).nonempty
    rw [mem_inter_iff] at hp
    have hp1 := (mem_membershipSet_iff _ k f p).mp hp.1
    have hp2 := (mem_membershipSet_iff P k g p).mp hp.2
    rcases (hsplit p hp1.1).2 with h1 | h2
    · exact h1.2 hp2.2
    · exact h2.2 hp1.2
  · -- Off `D₁` the witness is a.e. in `g`, hence a.e. in `f`, contradicting the split again.
    have hE : relativeComplement P (agreementSet P f g) ∩ relativeComplement P D₁ ∈ U :=
      hU.inter_mem hD hout
    have hEg : ∀ p ∈ relativeComplement P (agreementSet P f g) ∩ relativeComplement P D₁,
        p ∈ P ∧ k ‘ p ∈ g ‘ p ∧ k ‘ p ∉ f ‘ p := by
      intro p hp
      rw [mem_inter_iff] at hp
      obtain ⟨hpD, hpc⟩ := hp
      rw [mem_relativeComplement_iff] at hpc
      obtain ⟨-, hpD₁⟩ := hpc
      obtain ⟨hpP, hcase⟩ := hsplit p hpD
      rcases hcase with h1 | h2
      · exact absurd ((mem_membershipSet_iff _ k f p).mpr ⟨hpD, h1.1⟩) hpD₁
      · exact ⟨hpP, h2.1, h2.2⟩
    have hmemg : AEMem P U k g := by
      refine hU.mem_of_subset hE ?_ (membershipSet_subset P k g)
      intro p hp
      obtain ⟨hpP, hpg, -⟩ := hEg p hp
      exact (mem_membershipSet_iff P k g p).mpr ⟨hpP, hpg⟩
    have hmemf : AEMem P U k f := (h k hkA).mpr hmemg
    obtain ⟨p, hp⟩ := (hU.isNonempty_of_mem (hU.inter_mem hE hmemf)).nonempty
    rw [mem_inter_iff] at hp
    obtain ⟨-, -, hpf⟩ := hEg p hp.1
    exact hpf ((mem_membershipSet_iff P k f p).mp hp.2).2

end ZFVP
