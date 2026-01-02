import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor

namespace Bourbaki


-- ex1.1

example : TopologicalSpace Bool
where
  IsOpen B := B = ∅ ∨ B = Set.univ
  isOpen_univ := by simp
  isOpen_inter := by
    intro s t Hs Ht; simp
    rcases Hs with Hs | Hs<;>
    rcases Ht with Ht | Ht<;>
    subst s t<;> simp
  isOpen_sUnion := by
    intro s Hs
    by_contra F; simp at F; rcases F with ⟨F1, F2⟩
    rcases F1 with ⟨t, Ht, Ft⟩
    rcases Hs t Ht with Hs | Hs; contradiction
    subst t
    apply F2; ext x; simp
    use Set.univ, Ht; simp

example : TopologicalSpace Bool
where
  IsOpen B := True
  isOpen_univ := by simp
  isOpen_inter := by simp
  isOpen_sUnion := by simp


--ex1.3

section

def α [Topology X] (A : Set X) := interior (closure A)
def β [Topology X] (A : Set X) := closure (interior A)

lemma α_mono [Topology X] {A B : Set X} (h : A ⊆ B) :
  α A ⊆ α B
:= by
  simp [α]
  apply interior_mono
  apply closure_mono
  exact h

lemma β_mono [Topology X] {A B : Set X} (h : A ⊆ B) :
  β A ⊆ β B
:= by
  simp [β]
  apply closure_mono
  apply interior_mono
  exact h

lemma le_α [HX : Topology X] (A : Set X) (HA : HX.isOpen A) :
  A ⊆ α A
:= by
  simp [α]
  apply interior_le _ A _ HA
  intro x Hx
  rw [mem_closure_iff_adherent]
  intro B HB F
  simp [neighborOf, NeighborOf] at HB
  rcases HB with ⟨U, HU, Ux, UB⟩
  apply UB at Ux
  have HAB : x ∈ A ∩ B := by grind
  grind

lemma β_le [HX : Topology X] (A : Set X) (HA : HX.isClosed A) :
  β A ⊆ A
:= by
  simp [β]
  apply closure_le _ A HA
  intro x Hx
  simp [interior] at Hx
  rcases Hx with ⟨U, ⟨HU, UA⟩, Ux⟩
  apply UA Ux

lemma α_idem [HX : Topology X] (A : Set X) :
  α (α A) = α A
:= by
  apply subset_antisymm; swap
  · apply le_α
    simp [α]
    apply interior_isOpen
  · simp [α]
    apply interior_mono
    change β _ ⊆ _
    apply β_le
    apply closure_isClosed

lemma β_idem [HX : Topology X] (A : Set X) :
  β (β A) = β A
:= by
  apply subset_antisymm
  · apply β_le
    apply closure_isClosed
  · simp [β]
    apply closure_mono
    change _ ⊆ α _
    apply le_α
    apply interior_isOpen

lemma α_disjunction [HX : Topology X] (A B : Set X) (HA : HX.isOpen A) (HB : HX.isOpen B) :
  A ∩ B = ∅ → α A ∩ α B = ∅
:= by
  intro H
  simp [α]; ext x; simp
  intro Ax Bx
  have Bx' := mem_interior_iff_neighborOf.mp Bx
  rw [mem_interior_iff] at Ax
  rcases Ax with ⟨U, HU, EU⟩
  have Ux := neighborOf_mem_self HU
  have Ax : x ∈ closure A := by {
    by_contra F
    have : x ∈ U ∩ (closure A)ᶜ := by grind
    grind
  }
  rw [mem_closure_iff_adherent] at Ax
  apply Ax _ Bx'
  ext i; simp
  intro Ai HBi
  rw [isOpen_iff_eq_interior] at HA
  rw [<- HA, mem_interior_iff_neighborOf] at Ai
  rw [mem_closure_iff_adherent ] at HBi
  apply HBi _ Ai
  rw [Set.inter_comm, H]










end
