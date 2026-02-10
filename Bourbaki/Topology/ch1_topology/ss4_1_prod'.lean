import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod

namespace Bourbaki


def Prod.equiv (X Y : Type _) :
  X × Y ≃ biProd X Y
where
  toFun := fun p => fun b => match b with | true => p.fst | false => p.snd
  invFun := fun p => ⟨p true, p false⟩
  left_inv := by grind
  right_inv := by
    intro p; ext b; rcases b<;> simp

instance Prod.topology (X Y : Type _) [HX : Topology X] [HY : Topology Y] :
  Topology (X × Y)
:= by
  let HXY : Topology (biProd X Y) := (prod (fun b => cond b X Y))
  refine ⟨fun U => Prod.equiv X Y '' U ∈ Topology.isOpen, ?_, ?_, ?_⟩
  · intro s t; simp
    intro Hs Ht
    rw [Set.image_inter]
    apply HXY.isOpen_inter _ _ Hs Ht
    intro x y E; simp at E; grind
  · intro S HS; simp at HS
    rw [Set.image_sUnion]
    apply HXY.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨s', Hs', rfl⟩
    apply HS s' Hs'
  · simp
    apply HXY.isOpen_univ


lemma Prod.isOpen_iff [HX : Topology X] [HY : Topology Y] (U : Set (X × Y)) :
  U ∈ Topology.isOpen ↔  U ∈ (GenedTopology (Init.subbase (fun b p => Prod.equiv X Y p b))).isOpen
:= by
  constructor<;> intro H
  · unfold Topology.isOpen topology at H; simp at H
    change (Prod.equiv X Y) '' U ∈ Topology.isOpen at H
    rw [<- (Prod.equiv X Y).preimage_image U]
    set V := (Prod.equiv X Y) '' U
    suffices :  ∀ V ∈ (prod (fun b => cond b X Y)).isOpen, ⇑(Prod.equiv X Y) ⁻¹' V ∈ (GenedTopology (Init.subbase (fun b p => Prod.equiv X Y p b))).isOpen
    apply this V H
    clear H; intro V HV
    induction HV with
    | base U HU =>
      simp [Init.subbase, Init.to] at HU
      rcases HU with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; left
        use W, HW; ext p; simp
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; right
        use W, HW; ext p; simp
    | univ =>
      simp
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      rw [Set.preimage_inter]
      apply GenedOpen.inter<;> assumption
    | union S H IH =>
      rw [Set.preimage_sUnion]
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨s', Hs', rfl⟩
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨Hs', rfl⟩
      apply IH at Hs'
      exact Hs'
  · induction H with
    | base U HU =>
      simp [Init.subbase, Init.to] at HU
      rcases HU with ⟨V, HV, rfl⟩ | ⟨V, HV, rfl⟩
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; left
        use V, HV; ext p; simp
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; right
        use V, HV; ext p; simp
    | univ =>
      change Topology.isOpen (Set.univ : Set (X × Y))
      apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      change Topology.isOpen (S ∩ T)
      apply Topology.isOpen_inter S T IHS IHT
    | union S H IH =>
      change Topology.isOpen (⋃₀ S)
      apply Topology.isOpen_sUnion
      exact IH

def  Prod.Homeomorphic [HX : Topology X] [HY : Topology Y] :
  Homeomorphic (X × Y) (biProd X Y)
:= by
  apply Homeomorphic.mk (toEquiv := Prod.equiv X Y)
  · intro U HU
    change ((equiv X Y).toFun ⁻¹' U) ∈ Topology.isOpen
    rw [Prod.isOpen_iff]
    induction HU with
    | base V HV =>
      simp [Init.subbase, Init.to] at HV
      rcases HV with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; left
        use W, HW; ext p; simp
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; right
        use W, HW; ext p; simp
    | univ =>
      simp
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      rw [Set.preimage_inter]
      apply GenedOpen.inter _ _ IHS IHT
    | union S H IH =>
      rw [Set.preimage_sUnion]
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨s', Hs', rfl⟩
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨Hs', rfl⟩
      apply IH at Hs'
      exact Hs'
  · intro U HU
    change U ∈ Topology.isOpen at HU
    rw [Prod.isOpen_iff] at HU
    induction HU with
    | base V HV =>
      simp [Init.subbase, Init.to] at HV
      rcases HV with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; left
        use W, HW; ext p; simp
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]; right
        use W, HW; ext p; simp
    | univ =>
      change Topology.isOpen (Set.univ : Set (biProd X Y))
      apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp
      apply GenedOpen.inter _ _ IHS IHT
    | union S H IH =>
      simp
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨s', Hs', rfl⟩
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨Hs', rfl⟩
      apply IH at Hs'
      exact Hs'

lemma Prod.fst_isContinuous (X Y) [HX : Topology X] [HY : Topology Y] :
  IsContinuous (Prod.fst : X × Y → X)
:= by
  rw [IsContinuous_iff]
  intro U HU
  change (Prod.fst ⁻¹' U) ∈ (topology X Y).isOpen
  rw [Prod.isOpen_iff]
  apply GenedOpen.base
  simp [Init.subbase, Init.to]; right
  use U, HU; ext p; simp [equiv]

lemma Prod.snd_isContinuous (X Y) [HX : Topology X] [HY : Topology Y] :
  IsContinuous (Prod.snd : X × Y → Y)
:= by
  rw [IsContinuous_iff]
  intro U HU
  change (Prod.snd ⁻¹' U) ∈ (topology X Y).isOpen
  rw [Prod.isOpen_iff]
  apply GenedOpen.base
  simp [Init.subbase, Init.to]; left
  use U, HU; ext p; simp [equiv]


def Graph {X Y : Type _} (f : X → Y) (x : X) :
  {p : X × Y | p.snd = f p.fst}
:= ⟨⟨x, f x⟩, by simp⟩

lemma isContinuous_iff_isHomeomorphic_Graph  {X Y : Type u} [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  IsContinuous f ↔ IsHomeomorphic (Graph f)
:= by
  have Ef : Prod.snd ∘ Subtype.val ∘ Graph f = f := by ext x; simp [Graph]
  constructor<;> intro H
  · constructor
    · rw [IsContinuous_iff] at ⊢ H
      intro U HU
      rw [Subtopology.isOpen_eq] at HU
      rcases HU with ⟨V, HV, rfl⟩; simp [Graph]
      rw [Prod.isOpen_iff] at HV
      induction HV with
      | base U HU =>
        simp [Init.subbase, Init.to] at HU
        rcases HU with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩
        · change {a | (Prod.snd ∘ Subtype.val ∘ Graph f) a ∈ W} ∈ Topology.isOpen
          simp [Graph]
          apply H W HW
        · change {a | (Prod.fst ∘ Subtype.val ∘ Graph f) a ∈ W} ∈ Topology.isOpen
          simp [Graph]
          exact HW
      | univ =>
        simp; apply Topology.isOpen_univ
      | inter S T HS HT IHS IHT =>
        simp; rw [Set.setOf_and]
        apply Topology.isOpen_inter _ _ IHS IHT
      | union S H IH =>
        have : ⋃ s ∈ S, {a | ⟨a, f a⟩ ∈ s} = {a | (a, f a) ∈ ⋃₀ S} := by ext x; simp
        rw [<- this]
        apply Topology.isOpen_sUnion
        intro s Hs; simp at Hs
        rcases Hs with ⟨s', Hs', rfl⟩
        apply Topology.isOpen_sUnion
        intro s Hs; simp at Hs
        rcases Hs with ⟨Hs', rfl⟩
        apply IH s' Hs'
    · constructor
      · intro x y; simp [Graph]; grind
      · intro ⟨⟨x,y⟩, Hx⟩; simp at Hx; subst y
        use x; simp [Graph]
    · intro x U HU
      unfold neighborOf NeighborOf at HU ⊢ ; simp at HU ⊢
      rcases HU with ⟨V, HV, Vx, VU⟩
      have Hpr := Prod.fst_isContinuous X Y
      rw [IsContinuous_iff] at Hpr
      specialize Hpr V HV
      change (Prod.fst ⁻¹' V) ∈ (Prod.topology X Y).isOpen at Hpr
      use Graph f '' V; simp
      constructor; swap
      · constructor
        · use x
        · intro y Hy; simp
          use y, VU Hy
      · rw [Subtopology.isOpen_eq]
        use Prod.fst ⁻¹' V, Hpr
        ext p; simp
        constructor<;> intro Hp
        · rcases Hp with ⟨v, Hv, rfl⟩
          simp [Graph]
          exact Hv
        · rcases p with ⟨⟨x, y⟩, E⟩; simp at E Hp
          change x ∈ V at Hp
          use x, Hp
          simp [Graph]; rw [E]
  · rw [<- Ef]
    apply IsContinuous_comp; apply IsContinuous_comp
    · apply H.continuous
    · apply Subtopology.isContinuous
    · apply Prod.snd_isContinuous
