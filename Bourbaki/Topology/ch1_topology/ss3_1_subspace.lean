import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2

namespace Bourbaki

def Subtopology {X : Type _} [HX : Topology X] (A : Set X) :
  Topology A
where
  isOpen U := ∃ V ∈ HX.isOpen, U = Subtype.val ⁻¹' V
  isOpen_univ := by
    use Set.univ, HX.isOpen_univ; simp
  isOpen_inter S T := by
    intro ⟨S', HS', ES⟩ ⟨T', HT', ET⟩
    use S' ∩ T', HX.isOpen_inter _ _ HS' HT'
    ext x; simp; grind
  isOpen_union S HS := by
    choose! f Hf Hf' using HS
    use ⋃₀ {V | ∃ s ∈ S, V = f s}; constructor; swap
    · ext x; simp; grind
    · apply HX.isOpen_union
      intro V HV; simp at HV
      rcases HV with ⟨s, Hs, rfl⟩
      apply Hf s Hs

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

def subequiv {X : Type _} {A B  : Set X} (BA : B ⊆ A) :
  {x : A | x.val ∈ B} ≃  B
where
  toFun x := ⟨x.val.val, x.prop⟩
  invFun y := ⟨⟨y.val, BA y.prop⟩, y.prop⟩
  left_inv x := by simp
  right_inv y := by simp

example {A B : Type} (S : Set (Set A)) (HS : S.Nonempty) (f : A → B) (Hf : f.Injective) :
  ⋂ s ∈ S, (f '' s) ⊆ f '' (⋂₀ S)
:= by
  intro x Hx; simp at Hx; simp
  rcases HS with ⟨s, Hs⟩
  apply Hx at Hs
  rcases Hs with ⟨a, Ha, rfl⟩
  use a; simp
  intro t Ht
  apply Hx at Ht
  rcases Ht with ⟨b, Hb, E⟩
  apply Hf at E; subst b; assumption

lemma Subtopology.trans' [HX : Topology X] (A B : Set X) (BA : B ⊆ A):
  let _HA := Subtopology A
  ∀ U , U ∈ (Init.induced (Function.Embedding.subtype {x : A | x.val ∈ B})).isOpen
  ↔ (subequiv BA '' U) ∈ (Init.induced (Function.Embedding.subtype B)).isOpen
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
  change U ∈ (Init.topology gh).isOpen ↔ (subequiv BA '' U) ∈ (Init.topology f).isOpen
  constructor<;> intro H
  · rw [@Init.isOpen_iff] at H ⊢; simp at ⊢ H
    rcases H with ⟨V, HV, rfl⟩
    use (fun u => (subequiv BA) '' u) '' V
    constructor;swap
    · ext b; simp
    · intro s Hs; simp at *
      rcases Hs with ⟨v, Hv, rfl⟩
      apply HV at Hv; simp at Hv
      rcases Hv with ⟨W, HW, rfl⟩
      use Finset.image (fun u => (subequiv BA) '' u) W
      constructor
      · intro s Hs; simp at Hs
        simp [Init.subbase, f, Init.to]
        rcases Hs with ⟨w, Hw, rfl⟩
        apply HW at Hw
        simp [Init.subbase, gh, Init.to, g, h] at Hw
        rcases Hw with ⟨U, HU, rfl⟩
        use U, HU
        ext x; simp [subequiv]
        intro _; apply BA; simp
      · ext x
        rcases x with ⟨x, Bx⟩
        simp [subequiv]
        constructor<;> intro Hx; grind
        · use x, (BA Bx), Bx; grind
  · suffices : ∀ V , V ∈ (Init.topology f).isOpen → (subequiv BA).symm '' V ∈ (Init.topology gh).isOpen
    rw [<- Equiv.symm_image_image (subequiv BA) U]
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
      simp [subequiv]
    | univ =>
      simp; apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      simp [subequiv]
      rw [Set.image_inter]
      apply (Init.topology gh).isOpen_inter _ _ IHS IHT
      intro i j; grind
    | union S HS IH =>
      rw [Set.image_sUnion]
      apply (Init.topology gh).isOpen_union
      intro t Ht; simp at Ht
      rcases Ht with ⟨s, Ss, rfl⟩
      apply IH s Ss

lemma Subtopology.trans [HX : Topology X] (A B : Set X) (BA : B ⊆ A):
  let _HA := Subtopology A
  ∀ U , U ∈ (B.subtopologyOf A).isOpen ↔ (subequiv BA '' U) ∈ (Subtopology B).isOpen
:= by
  intro HA U
  unfold Topology.isOpen Set.subtopologyOf
  rw [Subtopology_eq_induced {x : A | ↑x ∈ B}, Subtopology_eq_induced B ]
  have E := Subtopology.trans' A B BA U
  unfold Topology.isOpen at E
  rw [E]


end Bourbaki
