import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2

namespace Bourbaki

def Subtopology {X : Type _} [HX : Topology X] (A : Set X) :
  Topology A
where
  isOpen U := ∃ V ∈ HX.isOpen, U = {x : A | x.val ∈ V}
  isOpen_univ := by
    use Set.univ, HX.isOpen_univ; simp
  isOpen_inter S T := by
    intro ⟨S', HS', ES⟩ ⟨T', HT', ET⟩
    use S' ∩ T', HX.isOpen_inter _ _ HS' HT'
    ext x; simp; grind
  isOpen_sUnion S HS := by
    choose! f Hf Hf' using HS
    use ⋃₀ {V | ∃ s ∈ S, V = f s}; constructor; swap
    · ext x; simp; grind
    · apply HX.isOpen_sUnion
      intro V HV; simp at HV
      rcases HV with ⟨s, Hs, rfl⟩
      apply Hf s Hs

lemma Subtopology.isOpen_iff {X : Type _} [HX : Topology X] {A : Set X} :
  ∀ U, U ∈ (Subtopology A).isOpen ↔ ∃ V ∈ HX.isOpen, U = {x : A | x.val ∈ V}
:= by intro U; rfl

lemma Subtopology_eq_induced {X : Type _} [HX : Topology X] (A : Set X) :
  Subtopology A = Init.induced (Function.Embedding.subtype A)
:= by
  unfold Init.induced
  apply le_antisymm
  · rw [<- @Init.IsContinuous_iff_le_inverse]
    rw [@IsContinuous_iff_IsOpen_preimage]
    intro U HU
    unfold Topology.isOpen Subtopology; simp
    use U, HU; rfl
  · intro U HU
    rcases HU with ⟨V, HV, E⟩
    apply GenedOpen.base
    simp [Init.subbase, Init.to]
    use V, HV,E

def _root_.Set.subtopologyOf {X : Type _} [HX : Topology X] (B A : Set X) :
  Topology {x : A | x.val ∈ B}
:= haveI := Subtopology A; Subtopology {x : A | x.val ∈ B}



def _root_.Set.Subset.equiv {X : Type _} {A B  : Set X} (BA : B ⊆ A) :
  {x : A | x.val ∈ B} ≃  B
where
  toFun x := ⟨x.val.val, x.prop⟩
  invFun y := ⟨⟨y.val, BA y.prop⟩, y.prop⟩
  left_inv x := by simp
  right_inv y := by simp

lemma Subtopology.trans' [HX : Topology X] (A B : Set X) (BA : B ⊆ A):
  let _HA := Subtopology A
  ∀ U , U ∈ (Init.induced (Function.Embedding.subtype {x : A | x.val ∈ B})).isOpen
  ↔ (BA.equiv '' U) ∈ (Init.induced (Function.Embedding.subtype B)).isOpen
:= by classical
  intro HA U
  unfold Topology.isOpen Init.induced Init.inverse; simp
  let h := fun _ : PUnit.{1} => (@Subtype.val ↑A {x | ↑x ∈ B})
  let g := fun (_ _ : PUnit.{1}) => @Subtype.val X A
  set f := fun _ : PUnit.{1} => @Subtype.val X B
  have E := Init.trans (h := h) (g := g)
  simp at E
  set HA' : _ → Topology ↑A := fun l : PUnit.{1} ↦ Init.topology fun ι : PUnit.{1} ↦ @Subtype.val X A
  have EA : (fun _ => HA) = HA' := by simp [HA', HA]; rw[Subtopology_eq_induced]; rfl
  rw [EA, <- E]; clear E EA HA'
  set gh := fun p : (PUnit.{1} × PUnit.{1}) ↦ g p.1 p.2 ∘ h p.1
  change U ∈ (Init.topology gh).isOpen ↔ (BA.equiv '' U) ∈ (Init.topology f).isOpen
  constructor<;> intro H
  · rw [@Init.isOpen_iff] at H ⊢; simp at ⊢ H
    rcases H with ⟨V, HV, rfl⟩
    use (fun u => (BA.equiv) '' u) '' V
    constructor;swap
    · ext b; simp
    · intro s Hs; simp at *
      rcases Hs with ⟨v, Hv, rfl⟩
      apply HV at Hv; simp at Hv
      rcases Hv with ⟨W, HW, rfl⟩
      use Finset.image (fun u => (BA.equiv) '' u) W
      constructor
      · intro s Hs; simp at Hs
        simp [Init.subbase, f, Init.to]
        rcases Hs with ⟨w, Hw, rfl⟩
        apply HW at Hw
        simp [Init.subbase, gh, Init.to, g, h] at Hw
        rcases Hw with ⟨U, HU, rfl⟩
        use U, HU
        ext x; simp [Set.Subset.equiv]
        intro _; apply BA; simp
      · ext x
        rcases x with ⟨x, Bx⟩
        simp [Set.Subset.equiv]
        constructor<;> intro Hx; grind
        · use x, (BA Bx), Bx; grind
  · suffices : ∀ V , V ∈ (Init.topology f).isOpen → (BA.equiv).symm '' V ∈ (Init.topology gh).isOpen
    rw [<- Equiv.symm_image_image (BA.equiv) U]
    apply this _ H
    intro V HV
    induction HV with
    | base U HU =>
      simp [Init.subbase, Init.to, f] at HU
      rcases HU with ⟨W, HW, rfl⟩
      apply GenedOpen.base
      simp [Init.subbase, Init.to, gh, g, h]
      use W, HW
      ext x; simp
      rcases x with ⟨⟨a, Aa⟩, Ba⟩; simp at Ba
      simp [Set.Subset.equiv]
    | univ =>
      simp; apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      simp [Set.Subset.equiv]
      rw [Set.image_inter]
      apply (Init.topology gh).isOpen_inter _ _ IHS IHT
      intro i j; grind
    | union S HS IH =>
      rw [Set.image_sUnion]
      apply (Init.topology gh).isOpen_sUnion
      intro t Ht; simp at Ht
      rcases Ht with ⟨s, Ss, rfl⟩
      apply IH s Ss

lemma Subtopology.trans [HX : Topology X] (A B : Set X) (BA : B ⊆ A):
  let _HA := Subtopology A
  ∀ U , U ∈ (B.subtopologyOf A).isOpen ↔ (BA.equiv '' U) ∈ (Subtopology B).isOpen
:= by
  intro HA U
  unfold Topology.isOpen Set.subtopologyOf
  rw [Subtopology_eq_induced {x : A | ↑x ∈ B}, Subtopology_eq_induced B ]
  have E := Subtopology.trans' A B BA U
  unfold Topology.isOpen at E
  rw [E]


lemma Subtopology.isOpen_iff_all [HX : Topology X] (A : Set X) :
  A ∈ HX.isOpen ↔ (∀ U ∈ (Subtopology A).isOpen, Subtype.val '' U ∈ HX.isOpen)
:= by
  conv => arg 2; arg 2; arg 1; unfold Topology.isOpen Subtopology; simp
  constructor<;> intro H; swap
  · specialize H Set.univ; simp at H
    apply H; use Set.univ; simp
    apply HX.isOpen_univ
  · intro B ⟨V, HV, E⟩
    rw [E]; simp [Set.image]
    apply HX.isOpen_inter _ _ HV H

lemma Subtopology.isClosed_iff [HX : Topology X] (A : Set X) :
  ∀ U, (Subtopology A).isClosed U ↔ ∃ V, HX.isClosed V ∧ U = {x : A | x.val ∈ V }
:= by
  intro U
  unfold Topology.isClosed Subtopology; simp
  constructor<;> intro ⟨V, HV, E⟩
  · use Vᶜ
    rw [compl_compl]
    use HV
    rw [<- compl_compl U, E]
    ext; simp
  · use Vᶜ, HV
    rw [E]; simp
    ext; simp

lemma Subtopology.neighborOf_iff [HX : Topology X] (A : Set X) (x : A) :
  ∀ U, U ∈ neighborOf (HX := Subtopology A) x ↔ ∃ V, V ∈ neighborOf (x.val) ∧ {x : A | x.val ∈ V} ⊆ U
:= by
  intro U
  unfold neighborOf NeighborOf; simp
  unfold Topology.isOpen Subtopology; simp
  unfold Topology.isOpen
  constructor<;> intro H
  · rcases H with ⟨V, HV,Vx, E⟩
    use V, ?_, E
    use V, HV
  · rcases H with ⟨V, ⟨W, HW, Wx, WV⟩, E⟩
    use W, HW, Wx
    intro a Ha; apply E; simp at *
    apply WV Ha

lemma Subtopology.neighbotOf_iff_all [HX : Topology X] (A : Set X) (x : A) :
  (∀ U, U ∈ neighborOf (HX := Subtopology A) x → Subtype.val '' U ∈ neighborOf x.val)
  ↔ A ∈ neighborOf x.val
:= by
  constructor<;> intro H
  · specialize H Set.univ; simp at H
    apply H
    unfold neighborOf NeighborOf; simp
    use Set.univ; simp
    apply (Subtopology A).isOpen_univ
  · intro U HU
    rw [neighborOf_iff] at HU
    rcases HU with ⟨V, HV, VU⟩
    unfold neighborOf NeighborOf at *; simp at *
    rcases HV with ⟨V', HV', Vx, VV⟩
    rcases H with ⟨A', HA', Ax, AA⟩
    have := Topology.isOpen_inter _ _ HA' HV'
    use A' ∩ V', this, ⟨Ax, Vx⟩
    intro i ⟨Ai, Vi⟩; simp
    use AA Ai; apply VU; simp
    apply VV Vi

lemma Subtopology.closure_eq [HX : Topology X] (A B : Set X) (BA : B ⊆ A) :
  closure (HX := Subtopology A) {x | x.val ∈ B}  = {x : A | x.val ∈ closure B}
:= by
  ext x; simp
  rw [@mem_closure_iff_adherent, @mem_closure_iff_adherent]
  constructor<;> intro Hx U HU FU
  · have : {x | x.val ∈ U} ∈ @neighborOf (↑A) (Subtopology A) x := by {
      rw [neighborOf_iff]; use U, HU
    }
    apply Hx _ this; ext i; simp
    intro Bi Ui
    have : i.val ∈ B ∩ U := by grind
    grind
  · rw [neighborOf_iff] at HU
    rcases HU with ⟨V, HV, VU⟩
    apply Hx _ HV
    ext i; simp
    intro Bi Vi
    let i' : A := ⟨i, BA Bi⟩
    have : i' ∈ {x : A | ↑x ∈ B} ∩ U := by {
      constructor<;> simp [i']; grind
      apply VU; simp; grind
    }
    grind

lemma IsDense_iff_subset_closure [HX : Topology X] (A B : Set X) (BA : B ⊆ A) :
  IsDense (HX := Subtopology A) {x : A | x.val ∈ B} ↔ A ⊆ closure B
:= by
  simp [IsDense]
  constructor<;> intro H
  · intro x Hx
    specialize H x Hx
    rw [Subtopology.closure_eq A B BA] at H; simp at H
    apply H
  · intro x Hx; rw [Subtopology.closure_eq A B BA]; simp
    apply H Hx






end Bourbaki
