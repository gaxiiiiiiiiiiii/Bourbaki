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
  apply le_interior _ A _ HA
  intro x Hx
  rw [mem_closure_iff]
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
  rw [mem_closure_iff] at Ax
  apply Ax _ Bx'
  ext i; simp
  intro Ai HBi
  rw [isOpen_iff_eq_interior] at HA
  rw [<- HA, mem_interior_iff_neighborOf] at Ai
  rw [mem_closure_iff ] at HBi
  apply HBi _ Ai
  rw [Set.inter_comm, H]


-- ex1.5

example [Topology X] (A : Set X) :
  frontier (closure A) ⊆ frontier A
:= by
  simp [frontier]
  rw [closure_idem]; simp
  apply subset_trans (b := closure (closure A)ᶜ); simp
  apply closure_mono
  rw [compl_closure]
  apply interior_le

example [Topology X] (A : Set X) :
  frontier (interior A) ⊆ frontier A
:= by
  simp [frontier]
  rw [compl_interior, closure_idem]; simp
  apply subset_trans (b := closure (interior A)); simp
  apply closure_mono
  apply interior_le


example [HX : Topology X] (A B : Set X) :
  frontier (A ∪ B) ⊆ frontier A ∪ frontier B
:= by
simp [frontier, closure_union]
rw [Set.union_inter_distrib_right]; simp
constructor
· intro x ⟨Hx, Hx'⟩; simp
  left; use Hx; clear Hx
  revert x
  change closure _ ⊆ closure _
  apply closure_mono; simp
· intro x ⟨Hx, Hx'⟩; simp
  right; use Hx; clear Hx
  revert x
  change closure _ ⊆ closure _
  apply closure_mono; simp

example [HX : Topology X] (A B : Set X) (H : closure A ∩ closure B = ∅) :
  frontier A ∪ frontier B ⊆ frontier (A ∪ B)
:= by
  simp [frontier, closure_union]
  constructor<;> constructor
  · apply subset_trans (b := closure A)<;> simp
  · apply subset_trans (b := closure B)<;> simp
  · intro x ⟨Hx, Hx'⟩
    have Fx : x ∉ closure B := by intro F; have : x ∈ closure A ∩ closure B := by {grind}; grind
    clear Hx
    rw [mem_closure_iff] at Fx Hx' ⊢; simp at Fx
    rcases Fx with ⟨V, HV, EV⟩
    intro U HU F
    have HUV := neighborOf_inter HU HV
    apply Hx' _ HUV
    ext i; simp
    intro Ai Ui Vi
    grind
  · intro x ⟨Hx, Hx'⟩
    have Fx : x ∉ closure A := by intro F; have : x ∈ closure A ∩ closure B := by {grind}; grind
    rw [mem_closure_iff] at Fx Hx' Hx ⊢; simp at Fx
    rcases Fx with ⟨V, HV, EV⟩
    intro U HU F
    have HUV := neighborOf_inter HU HV
    apply Hx' _ HUV
    ext i; simp
    intro Bi Ui Vi
    grind

example [HX : Topology X]  (A B : Set X) (HA : HX.isOpen A) (HB : HX.isOpen B) :
  (A ∩ frontier B) ∪ (B ∩ frontier A) ⊆ frontier (A ∩ B)
:= by
  simp [frontier]
  constructor<;> constructor<;>
  intro x ⟨Hx, H, H'⟩<;>
  rw [mem_closure_iff] at H H' ⊢<;>
  intro U HU F
  · rw [isOpen_iff_eq_interior] at HA
    rw [<- HA, mem_interior_iff_neighborOf] at Hx
    have HAU := neighborOf_inter HU Hx
    specialize H _ HAU
    grind
  · rw [isOpen_iff_eq_interior] at HB
    rw [<- HB, mem_interior_iff_neighborOf] at Hx
    have HBU := neighborOf_inter HU Hx
    specialize H' _ HBU
    grind
  · rw [isOpen_iff_eq_interior] at HA
    rw [<- HA, mem_interior_iff_neighborOf] at Hx
    have HAU := neighborOf_inter HU Hx
    specialize H' _ HAU
    grind
  · rw [isOpen_iff_eq_interior] at HB
    rw [<- HB, mem_interior_iff_neighborOf] at Hx
    have HBU := neighborOf_inter HU Hx
    specialize H _ HBU
    grind

example [HX : Topology X]  (A B : Set X) (HA : HX.isOpen A) (HB : HX.isOpen B) :
  frontier (A ∩ B) ⊆ (A ∩ frontier B) ∪ (B ∩ frontier A) ∪ (frontier A ∩ frontier B)
:= by
  intro x ⟨H1, H2⟩; simp
  rw [mem_closure_iff] at H1 H2
  by_cases Ax : x ∈ A
  · left; left; use Ax
    rw [mem_frontier_iff]
    intro U HU
    constructor<;> intro F
    · have Ux := neighborOf_mem_self HU
      apply H1 U HU
      rw [Set.inter_assoc, F]; simp
    · have Ux := neighborOf_mem_self HU
      have Bx : x ∈ B := by by_contra F; have : x ∈ Bᶜ ∩ U := by {grind}; grind
      rw [isOpen_iff_eq_interior] at HB HA
      rw [<- HB, mem_interior_iff_neighborOf] at Bx
      rw [<- HA, mem_interior_iff_neighborOf] at Ax
      have HAB := neighborOf_inter Ax Bx
      apply H2 _ HAB
      simp
  by_cases Bx : x ∈ B
  · left; right; use Bx
    rw [mem_frontier_iff]
    intro U HU
    constructor<;> intro F
    · have Ux := neighborOf_mem_self HU
      apply H1 U HU
      rw [Set.inter_comm A B, Set.inter_assoc, F]; simp
    · have Ux := neighborOf_mem_self HU
      have Ax : x ∈ A := by by_contra F; have : x ∈ Aᶜ ∩ U := by {grind}; grind
      rw [isOpen_iff_eq_interior] at HA HB
      rw [<- HA, mem_interior_iff_neighborOf] at Ax
      rw [<- HB, mem_interior_iff_neighborOf] at Bx
      have HAB := neighborOf_inter Ax Bx
      apply H2 _ HAB
      simp
  · right
    rw [mem_frontier_iff, mem_frontier_iff]
    constructor<;> intro U HU<;> constructor<;> intro F
    · apply H1 U HU
      rw [Set.inter_comm A B, Set.inter_assoc, F]; simp
    · have Ux := neighborOf_mem_self HU
      have : x ∈ Aᶜ ∩ U := by grind
      grind
    · apply H1 U HU
      rw [Set.inter_assoc, F]; simp
    · have Ux := neighborOf_mem_self HU
      have : x ∈ Bᶜ ∩ U := by grind
      grind


-- ex1.6

example [HX : Topology X] (A : Set X) :
  (∀ U, IsDense U → A ∩ U ≠ ∅) ↔ interior A ≠ ∅
:= by
  unfold IsDense
  constructor<;> intro H
  · intro F
    apply H Aᶜ; swap; simp
    intro x
    rw [mem_closure_iff]
    intro U HU FU
    have Ux := neighborOf_mem_self HU
    have Ax : x ∈ A := by by_contra Fx; have : x ∈ Aᶜ ∩ U := by {grind}; grind
    have : x ∉ interior A := by intro Fx; grind
    rw [mem_interior_iff] at this; simp at this
    apply this U HU
    rw [Set.inter_comm, FU]
  · intro U HU F
    apply H; clear H
    ext x; simp
    intro Ax
    specialize HU x
    rw [mem_closure_iff] at HU
    rw [mem_interior_iff_neighborOf] at Ax
    apply HU A Ax
    rw [Set.inter_comm, F]

-- ex1.8
example [HX : Topology X] (A : Set X) :
  isolate A = ∅ → isolate (closure A) = ∅
:= by
  intro H; ext x; simp
  intro Hx
  simp [isolate] at Hx H
  rcases Hx with ⟨Hx, Fx⟩
  rw [mem_closure_iff] at Hx Fx
  apply Fx; clear Fx
  intro U HU F
  apply Hx _ HU
  rw [<- F]
  apply Set.inter_congr_right
  · intro y; simp
    intro Hy Fy Uy
    by_contra FA; apply Fy; clear Fy
    have Fy : y ∉ closure A \ {x} := by intro F; have : y ∈ closure A \ {x} ∩ U := by {grind}; grind
    simp at Fy
    apply Fy Hy
  · intro y ⟨Ay, Uy⟩
    simp; constructor; swap
    · intro E; subst y
      specialize H x Ay
      rw [mem_closure_iff] at H
      apply H U HU
      ext y; simp
      intro Ay' E Uy'
      have Fy : y ∉ closure A \ {x} := by intro F; have : y ∈ closure A \ {x} ∩ U := by {grind}; grind
      apply Fy; simp; clear Fy
      use ?_, E
      rw [mem_closure_iff]
      intro V HV AV
      have Vy := neighborOf_mem_self HV
      have Ax : y ∉ A := by by_contra F; have : y ∈ A ∩ V := by {grind}; grind
      contradiction
    · rw [mem_closure_iff]
      intro V HV AV
      have Vy := neighborOf_mem_self HV
      have Fy : y ∈ A ∩ V := by grind
      grind
