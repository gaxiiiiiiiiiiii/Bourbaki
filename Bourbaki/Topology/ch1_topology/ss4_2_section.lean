import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod
import Bourbaki.Topology.ch1_topology.ss4_1_prod'

namespace Bourbaki

def constFst_Homeomorphic' (X₁ X₂ : Type _) [HX₁ : Topology X₁] [HX₂ : Topology X₂] (a₁ : X₁) :
  Homeomorphic X₂ {p : X₁ × X₂ | p.fst = a₁}
where
  toFun := fun x₂ => ⟨⟨a₁, x₂⟩, by simp⟩
  invFun := fun p => p.val.2
  left_inv := by intro x; simp
  right_inv := by
    intro p; simp
    rcases p with ⟨⟨x₁, x₂⟩, Hp⟩; simp at Hp
    subst a₁; simp
  continuous_fun := by
    intro U HU
    rw [Subtopology.isOpen_eq] at HU
    rcases HU with ⟨V, HV, rfl⟩
    simp
    rw [Prod.isOpen_iff] at HV
    induction HV with
    | base U HU =>
      simp [Init.subbase, Init.to] at HU
      rcases HU with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩<;> simp [Prod.equiv]
      · exact HW
      · set U := {a : X₂ | a₁ ∈ W}
        by_cases Ha : a₁ ∈ W
        · have : U = Set.univ := by ext x; simp [U]; assumption
          rw [this]; apply Topology.isOpen_univ
        · have : U = ∅ := by ext x; simp [U]; assumption
          rw [this]; apply Topology.isOpen_empty
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; rw [Set.setOf_and]
      apply Topology.isOpen_inter _ _ IHS IHT
    | union S H IH =>
      have : ⋃ s ∈ S, {a | ⟨a₁, a⟩ ∈ s} = {a | (a₁, a) ∈ ⋃₀ S} := by ext x; simp
      rw [<- this]
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨s', Hs', rfl⟩
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨Hs', rfl⟩
      apply IH s' Hs'
  continuous_inv := by
    intro U HU
    rw [Subtopology.isOpen_eq]
    use Prod.snd ⁻¹' U
    constructor
    · rw [Prod.isOpen_iff]
      apply GenedOpen.base
      simp [Init.subbase, Init.to]
      left
      use U, HU; simp [Prod.equiv]
    · ext p; simp


def Prod.mk (X₁ X₂ : Type _)(a : X₁) :
  X₂ → X₁ × X₂
:= _root_.Prod.mk a

def Prod.mkFlip (X₁ X₂ : Type _)(a : X₂) :
  X₁ → X₁ × X₂
:= fun x => _root_.Prod.mk x a


lemma Prod.mk_isContinuous (X₁ X₂ : Type _) [HX₁ : Topology X₁] [HX₂ : Topology X₂] (a : X₁) :
  IsContinuous (Prod.mk X₁ X₂ a)
:= by
  rw [IsContinuous_iff]; intro U (HU : U ∈ Topology.isOpen)
  rw [Prod.isOpen_iff] at HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩<;> simp [Prod.equiv]
    · exact HW
    · set U := ((Prod.mk X₁ X₂ a) ⁻¹' ((fun p : X₁ × X₂ ↦ p.1) ⁻¹' W))
      by_cases Ha : a ∈ W
      · have : U = Set.univ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_univ
      · have : U = ∅ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_empty
  | univ =>
    simp; apply Topology.isOpen_univ
  | inter S T HS HT IHS IHT =>
    simp
    apply Topology.isOpen_inter _ _ IHS IHT
  | union S H IH =>
    simp
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨s', Hs', rfl⟩
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨Hs', rfl⟩
    apply IH s' Hs'

lemma Prod.mkFlip_isContinuous (X₁ X₂ : Type _) [HX₁ : Topology X₁] [HX₂ : Topology X₂] (a : X₂) :
  IsContinuous (Prod.mkFlip X₁ X₂ a)
:= by
  rw [IsContinuous_iff]; intro U (HU : U ∈ Topology.isOpen)
  rw [Prod.isOpen_iff] at HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩<;> simp [Prod.equiv]
    · set U := ((Prod.mkFlip X₁ X₂ a) ⁻¹' ((fun p : X₁ × X₂ ↦ p.2) ⁻¹' W))
      by_cases Ha : a ∈ W
      · have : U = Set.univ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_univ
      · have : U = ∅ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_empty
    · exact HW
  | univ =>
    simp; apply Topology.isOpen_univ
  | inter S T HS HT IHS IHT =>
    simp
    apply Topology.isOpen_inter _ _ IHS IHT
  | union S H IH =>
    simp
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨s', Hs', rfl⟩
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨Hs', rfl⟩
    apply IH s' Hs'


def Prod.mk_homeomorphic (X₁ X₂ : Type _) [HX₁ : Topology X₁] [HX₂ : Topology X₂] (a : X₁):
  Homeomorphic X₂ (Quotient (Setoid.ker (Prod.snd (α := X₁) (β := X₂))))
where
  toFun := fun x => ⟦⟨a, x⟩⟧
  invFun := fun x => by
    apply Quotient.liftOn x Prod.snd
    intro p₁ p₂ E; exact E
  left_inv := by intro x; simp
  right_inv := by
    intro x; simp
    rw [<- Quotient.out_eq x, Quotient.liftOn_mk, Quotient.eq]; simp
  continuous_fun := by
    intro U HU
    change U ∈ Topology.isOpen at HU
    rw [Quotspace.isOpen_iff] at HU
    let h := Quotient.mk (Setoid.ker (Prod.snd (α := X₁) (β := X₂))) ∘ (fun x₂ => ⟨a, x₂⟩)
    set g := fun x : X₂ => Quotient.mk (Setoid.ker (Prod.snd (α := X₁) (β := X₂))) ⟨a, x⟩
    have E : g = h := by ext x; simp [g, h]
    rw [E]; simp [h]; rw [Set.preimage_comp]
    have := mk_isContinuous X₁ X₂ a
    rw [IsContinuous_iff] at this
    apply this _ HU
  continuous_inv := by
    intro U HU
    change _ ∈ (Finale.quotient (Setoid.ker (Prod.snd))).isOpen
    rw [Quotspace.isOpen_iff]
    rw [Prod.isOpen_iff]
    apply GenedOpen.base
    simp [Init.subbase, Init.to]
    left; use U, HU
    ext p; simp [Prod.equiv]


def Prod.mk_section (X₁ X₂) [HX₁ : Topology X₁] [HX₂ : Topology X₂] (a₁ : X₁) :
  ContinuousSection (Quotient.mk (Setoid.ker (Prod.snd (α := X₁) (β := X₂))))
where
  sect := Prod.mk X₁ X₂ a₁ ∘ (mk_homeomorphic X₁ X₂ a₁).invFun
  right_inverse := by
    ext x; simp [Prod.mk_homeomorphic]
    rw [<- Quotient.out_eq x, Quotient.liftOn_mk]
    rw [Quotient.eq]; simp [Prod.mk]
  continuous := by
    apply IsContinuous_comp
    · rw [IsContinuous_iff]
      apply (mk_homeomorphic X₁ X₂ a₁).continuous_inv
    · apply mk_isContinuous


lemma Prod.slice_isOpen [Topology X] [Topology Y] (a : X) (U : Set (X × Y)) :
  U ∈ Topology.isOpen → {y : Y | ⟨a, y⟩ ∈ U} ∈ Topology.isOpen
:= by
  intro HU
  have := Prod.mk_isContinuous X Y a
  rw [IsContinuous_iff] at this
  specialize this U HU
  have E : {y : Y | ⟨a, y⟩ ∈ U} = (Prod.mk X Y a) ⁻¹' U := by ext x; simp [Prod.mk]
  rw [E]; exact this


lemma Pord.snd_image_eq_sUnion (X Y : Type _) (S : Set (X × Y)) :
  Prod.snd '' S = ⋃ x : X, {y : Y | ⟨x, y⟩ ∈ S}
:= by ext y; simp

lemma Prod.fst_image_eq_sUnion (X Y : Type _) (S : Set (X × Y)) :
  Prod.fst '' S = ⋃ y : Y, {x : X | ⟨x, y⟩ ∈ S}
:= by ext x; simp


lemma Prod.snd_isOpen [Topology X] [Topology Y] (U : Set (X × Y)) :
  U ∈ Topology.isOpen → Prod.snd '' U ∈ Topology.isOpen
:= by
  intro HU; rw [Pord.snd_image_eq_sUnion]
  apply Topology.isOpen_sUnion
  intro s Hs; simp at Hs
  rcases Hs with ⟨x, rfl⟩
  have := Prod.mk_isContinuous X Y x
  rw [IsContinuous_iff] at this
  specialize this U HU
  have E : {y : Y | ⟨x, y⟩ ∈ U} = (Prod.mk X Y x) ⁻¹' U := by ext y; simp [mk]
  rw [E]; exact this


lemma Prod.fst_isOpen [Topology X] [Topology Y] (U : Set (X × Y)) :
  U ∈ Topology.isOpen → Prod.fst '' U ∈ Topology.isOpen
:= by
  intro HU; rw [Prod.fst_image_eq_sUnion]
  apply Topology.isOpen_sUnion
  intro s Hs; simp at Hs
  rcases Hs with ⟨y, rfl⟩
  rw [Prod.isOpen_iff] at HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨W, HW, rfl⟩ | ⟨W, HW, rfl⟩<;> simp [Prod.equiv]
    · set U := {x : X | y ∈ W }
      by_cases Hy : y ∈ W
      · have : U = Set.univ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_univ
      · have : U = ∅ := by ext x; simp [U]; assumption
        rw [this]; apply Topology.isOpen_empty
    · exact HW
  | univ =>
    simp; apply Topology.isOpen_univ
  | inter S T HS HT IHS IHT =>
    simp
    apply Topology.isOpen_inter _ _ IHS IHT
  | union S H IH =>
    have : {x | (x, y) ∈ ⋃₀ S} = ⋃ s ∈ S, {x | (x, y) ∈ s} := by ext x; simp
    rw [this]
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨s', Hs', rfl⟩
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨Hs', rfl⟩
    apply IH s' Hs'

lemma Prod.isContinuousAt_snd [HX₁ : Topology X₁] [HX₂ : Topology X₂] [HY : Topology Y]
  (f : X₁ × X₂ → Y) (a₁ : X₁) (a₂ : X₂) :
  IsContinuousAt f (a₁, a₂) → IsContinuousAt (fun x₂ => f (a₁, x₂)) a₂
:= by
  intro H
  have : (fun x₂ ↦ f (a₁, x₂)) = f ∘ Prod.mk X₁ X₂ a₁ := by ext x; simp [mk]
  rw [this]; clear this
  apply IsContinuousAt_comp
  · apply Prod.mk_isContinuous X₁ X₂ a₁ a₂
  · simp [mk]; exact H

lemma Prod.isContinuousAt_fst [HX₁ : Topology X₁] [HX₂ : Topology X₂] [HY : Topology Y]
  (f : X₁ × X₂ → Y) (a₁ : X₁) (a₂ : X₂) :
  IsContinuousAt f (a₁, a₂) → IsContinuousAt (fun x₁ => f (x₁, a₂)) a₁
:= by
  intro H
  have : (fun x₁ ↦ f (x₁, a₂)) = f ∘ Prod.mkFlip X₁ X₂ a₂ := by ext x; simp [mkFlip]
  rw [this]; clear this
  apply IsContinuousAt_comp
  · apply Prod.mkFlip_isContinuous X₁ X₂ a₂ a₁
  · simp [mkFlip]; exact H
