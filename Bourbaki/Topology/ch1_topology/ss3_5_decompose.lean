import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace
import Bourbaki.Topology.ch1_topology.ss3_2_continuous
import Bourbaki.Topology.ch1_topology.ss3_3_locallyClosed
import Bourbaki.Topology.ch1_topology.ss3_4_quatient
import Bourbaki.Misc

namespace Bourbaki


section decompose

def kerLift [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  Quotient (Setoid.ker f) → Set.range f
:= fun x => by
  apply Quotient.liftOn x (fun x => ⟨f x, by simp⟩)
  intro a b H; ext; simp
  rw [<- Setoid.ker_def]
  exact H

lemma kerLift_bijective [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  (kerLift f).Bijective
:= by
  constructor
  · intro a b
    rw [<- Quotient.out_eq a, <- Quotient.out_eq b]
    simp only [kerLift]; rw [Quotient.liftOn_mk, Quotient.liftOn_mk]
    intro H; simp at H
    rw [Quotient.eq, Setoid.ker_def, H]
  · intro ⟨y, Hy⟩; simp at Hy
    rcases Hy with ⟨x, Hx⟩
    use ⟦x⟧; simp only [kerLift]
    rw [Quotient.liftOn_mk]; simp
    rw [Hx]

def decompose [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  X → Y
:= (Subtype.val) ∘ (kerLift f) ∘ Quotient.mk (Setoid.ker f)

lemma decompose_eq [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  decompose f = f
:= by ext x; simp [decompose, kerLift]


lemma decompose_IsTopologyHom_iff_isOpen [HX : Topology X] [HY : Topology Y] (f : X → Y) (Hf : IsContinuous f) :
  IsTopologyHom (kerLift f) ↔
  ∀ U ∈ HX.isOpen, IsSaturated f U →  ({x : Set.range f | x.val ∈ f '' U} ∈ (Subtopology (Set.range f)).isOpen)
:= by
  constructor<;> intro H
  · intro U HU HfU
    rw [Subtopology.isOpen_eq]; simp
    have H2 := H.topologyHom.continuous_inv
    set σ := H.topologyHom.toEquiv

    rw [IsSaturated_iff_eq_preimage_image] at HfU
    rw [<- HfU, <- Quotspace.isOpen_iff] at HU
    apply H2 at HU
    rw [Subtopology.isOpen_eq] at HU
    rcases HU with ⟨V, HV, E⟩
    use V, HV
    rw [<- E]; simp
    rw [<- σ.image_eq_preimage_symm]
    simp [σ, IsTopologyHom.topologyHom]
    ext x; simp [kerLift]; grind
  ·
    let E := Equiv.ofBijective _ (kerLift_bijective f)
    let H : TopologyHom (Quotient (Setoid.ker f)) (Set.range f) := by {
      apply TopologyHom.mk (toEquiv := E)
      · intro U HU
        rw [Subtopology.isOpen_eq] at HU
        rcases HU with ⟨V, HV, rfl⟩; simp
        change {a | ↑(E a) ∈ V} ∈ Topology.isOpen
        rw [Finale.isOpen_iff]; simp [E]
        rw [ Set.preimage_setOf_eq (f := (Quotient.mk (Setoid.ker f)))]
        have : {a | ↑(kerLift f ⟦a⟧) ∈ V} = f ⁻¹' V := by ext x; simp [kerLift]
        rw [this]; clear this
        rw [IsContinuous_iff_IsOpen_preimage] at Hf
        apply Hf V HV
      · intro U HU
        change _ ∈ (Subtopology (Set.range f)).isOpen
        rw [Subtopology.isOpen_eq]; simp
        change U ∈ Topology.isOpen at HU
        rw [Finale.isOpen_iff] at HU; simp at HU

        have : IsSaturated f (Quotient.mk (Setoid.ker f) ⁻¹' U) := by {
          intro x Hx y Hy; simp at Hx Hy ⊢
          suffices : (⟦y⟧ : Quotient (Setoid.ker f)) = ⟦x⟧; rw [this]; assumption
          rw [Quotient.eq, Setoid.ker_def, Hy]
        }
        specialize H ((Quotient.mk (Setoid.ker f) ⁻¹' U)) HU this
        rw [Subtopology.isOpen_eq] at H; simp at H
        rcases H with ⟨V, HV, EV⟩
        use V, HV; rw [<- EV, <- Equiv.image_eq_preimage_symm]
        ext x; simp [E, kerLift]
        rcases x with ⟨x, y, rfl⟩; simp
        constructor<;> intro Hx
        · rcases Hx with ⟨u, Hu, E⟩
          rw [<- Quotient.out_eq u, Quotient.liftOn_mk] at E; simp at E
          use u.out; rw [E]; simp; assumption
        · rcases Hx with ⟨u, Hu, E⟩
          use ⟦u⟧, Hu
          rw [Quotient.liftOn_mk]; simp
          rw [E]
    }
    apply H.isTopologyHom


lemma decompose_IsTopologyHom_iff_isClosed [HX : Topology X] [HY : Topology Y] (f : X → Y) (Hf : IsContinuous f) :
  IsTopologyHom (kerLift f) ↔
  ∀ U, HX.isClosed U → IsSaturated f U →   (Subtopology (Set.range f)).isClosed {x : Set.range f | x.val ∈ f '' U}
:= by
  unfold Topology.isClosed
  rw [decompose_IsTopologyHom_iff_isOpen f Hf]
  constructor<;> intro H U HU HfU
  · have HfU' : IsSaturated f Uᶜ := by {
      intro x Hx y H F; apply Hx
      apply HfU y F x H.symm
    }
    have := H Uᶜ HU HfU'
    rw [Subtopology.isOpen_eq] at this ⊢; simp at this ⊢
    rcases this with ⟨V, HV, E⟩
    use V, HV
    ext y; simp
    constructor<;> intro Hy
    · have : y ∈ {x : Set.range f | ∃ x_1 ∉ U, f x_1 = ↑x} := by simp; grind
      grind
    · have : y ∈ {x : Set.range f | x.val ∈ V} := by grind
      rw [<- E] at this; simp at this
      intro x Hx F
      rcases this with ⟨z, Hz, Ez⟩
      apply Hz
      apply HfU x Hx z
      simp; rw [F, <- Ez]
  · have HfU' : IsSaturated f Uᶜ := by {
      intro x Hx y H F; apply Hx
      apply HfU y F x H.symm
    }
    have := H Uᶜ (by simp; exact HU) HfU'
    rw [Subtopology.isOpen_eq] at this ⊢; simp at this ⊢
    rcases this with ⟨V, HV, E⟩
    use V, HV
    ext y; simp
    constructor<;> intro Hy
    · have : y ∈ {x : Set.range f | ∃ x_1 ∉ U, f x_1 = ↑x}ᶜ := by {
        simp; intro x Fx F; apply Fx; clear Fx
        rcases Hy with ⟨x', Hx', Ex'⟩
        apply HfU x' Hx'; simp
        rw [F, Ex']
      }
      rw [E] at this; simp at this
      exact this
    · have : y ∈ {x : Set.range f | x.val ∈ V} := by grind
      rw [<- E] at this; simp at this
      rcases y with ⟨y, Hy'⟩; simp at Hy'
      rcases Hy' with ⟨x, rfl⟩; simp at Hy this ⊢
      by_cases Ux : x ∈ U
      · use x, Ux
      · specialize this x Ux; contradiction


--　ブルバキ位相では、連続断面なる概念を使ってて、たぶん右逆像gで良さそう
-- fの全射性から存在がいえる右逆写像が連続としてもよいけど、noncomputableになるのを避けた
structure ContinuousSection [HX : Topology X] [HY : Topology Y] (f : X → Y) where
  sect : Y → X
  continuous : IsContinuous sect
  right_inverse : f ∘ sect = id

lemma ContinuousSection.kerLift_IsTopologyHom [HX : Topology X] [HY : Topology Y]
  (f : X → Y) (Hf : IsContinuous f) (s : ContinuousSection f) :
  IsTopologyHom (kerLift f)
where
  continuous := by
    rw [IsContinuous_iff_IsOpen_preimage]
    intro U HU
    rw [Subtopology.isOpen_eq] at HU
    change (kerLift f ⁻¹' U) ∈ Topology.isOpen
    rw [Finale.isOpen_iff]; simp
    rcases HU with ⟨V, HV, rfl⟩; simp
    rw [ Set.preimage_setOf_eq (f := (Quotient.mk (Setoid.ker f)))]
    have : {a | ↑(kerLift f ⟦a⟧) ∈ V} = f ⁻¹' V := by ext x; simp [kerLift]
    rw [this]; clear this
    rw [IsContinuous_iff_IsOpen_preimage] at Hf
    apply Hf V HV
  bij := by
    constructor
    · intro x y
      rw [<- Quotient.out_eq x, <- Quotient.out_eq y]
      simp only [kerLift]
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk]
      intro H; simp at H
      rw [Quotient.eq, Setoid.ker_def, H]
    · intro y; rcases y with ⟨y, Hy⟩; simp at Hy
      rcases Hy with ⟨x, rfl⟩
      use ⟦x⟧; simp [kerLift]
  open_map := by
    intro x U HU
    have Hs := s.continuous
    unfold neighborOf NeighborOf at HU ⊢; simp at HU ⊢
    rcases HU with ⟨V, HV, Vx, VU⟩
    change V ∈ Topology.isOpen at HV
    rw [Finale.isOpen_iff] at HV; simp at HV
    rw [IsContinuous_iff_IsOpen_preimage] at Hs
    apply Hs at HV
    use @Subtype.val Y (Set.range f) ⁻¹' (s.sect ⁻¹' (Quotient.mk (Setoid.ker f) ⁻¹' V))
    constructor
    · change (Subtype.val ⁻¹' (s.sect ⁻¹' (Quotient.mk (Setoid.ker f) ⁻¹' V))) ∈ (Subtopology (Set.range f)).isOpen
      rw [Subtopology.isOpen_eq]; simp
      use (s.sect ⁻¹' (Quotient.mk (Setoid.ker f) ⁻¹' V)); simp
      use HV
      ext y; simp
    constructor
    · simp [kerLift]
      rw [<- Quotient.out_eq x, Quotient.liftOn_mk]; simp
      suffices : (⟦s.sect (f x.out)⟧ : Quotient (Setoid.ker f)) = ⟦x.out⟧
      rw [this, Quotient.out_eq x]; exact Vx
      rw [Quotient.eq, Setoid.ker_def]
      have := congr_fun s.right_inverse (f x.out); simp at this
      rw [this]
    · intro y Hy; simp at Hy ⊢
      use ⟦s.sect y⟧, (VU Hy)
      simp [kerLift]; ext; simp
      have := congr_fun s.right_inverse y; simp at this
      rw [this]


def ContinuousSection.TopologyHom [HX : Topology X] [HY : Topology Y]
  (f : X → Y) (Hf : IsContinuous f) (s : ContinuousSection f) :
  TopologyHom Y (Set.range s.sect)
where
  toFun := fun y => ⟨s.sect y, by simp⟩
  invFun := fun x => f x.val
  right_inv := by
    intro x; simp; ext; simp
    rcases x with ⟨x, Hx⟩; simp at Hx
    rcases Hx with ⟨y, rfl⟩; simp
    have := congr_fun s.right_inverse y; simp at this
    rw [this]
  left_inv := by
    intro y; simp
    have := congr_fun s.right_inverse y; simp at this
    rw [this]
  continuous_fun := by
    intro U HU
    have Hs := s.continuous
    rw [Subtopology.isOpen_eq] at HU
    rcases HU with ⟨V, HV, rfl⟩; simp
    rw [IsContinuous_iff_IsOpen_preimage] at Hs
    apply Hs V HV
  continuous_inv := by
    intro U HU
    rw [Subtopology.isOpen_eq]
    rw [IsContinuous_iff_IsOpen_preimage] at Hf
    specialize Hf U HU
    use f ⁻¹' U, Hf; simp
    ext x; simp


end decompose

end Bourbaki
