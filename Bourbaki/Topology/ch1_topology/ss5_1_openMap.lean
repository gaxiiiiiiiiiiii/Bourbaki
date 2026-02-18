import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4



open Bourbaki

def IsOpenmap [HX : Topology X] [HY : Topology Y] (f : X → Y) : Prop :=
  ∀ U, HX.isOpen U → HY.isOpen (f '' U)

def IsClosedmap [HX : Topology X] [HY : Topology Y] (f : X → Y) : Prop :=
  ∀ F, HX.isClosed F → HY.isClosed (f '' F)

lemma IsOpenmap_iff_neighborOf [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  IsOpenmap f ↔ ∀ x U, U ∈ neighborOf x → f '' U ∈ neighborOf (f x)
:= by
  simp [IsOpenmap]
  constructor<;> intro H
  · intro x U HU
    unfold neighborOf NeighborOf at HU ⊢; simp at HU ⊢
    rcases HU with ⟨V, HV, Vx, VB⟩
    use f '' V, H V HV
    grind
  · intro U HU
    rw [<- mem_neighbor_iff_isOpen] at ⊢ HU
    intro x Hx; rcases Hx with ⟨y, Hy, rfl⟩
    apply H; apply HU y Hy

lemma IsHomeomorphic_iff  [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  IsHomeomorphic f ↔ (IsContinuous f ∧ f.Bijective ∧ IsOpenmap f)
:= by
  rw [IsOpenmap_iff_neighborOf]
  constructor<;> intro H
  · use H.1, H.2, H.3
  · use H.1, H.2.1, H.2.2

lemma Subtopology.isOpenmap [HX : Topology X] (A : Set X) :
  IsOpenmap (Subtype.val : A → X) ↔ A ∈ Topology.isOpen
:= by
  unfold IsOpenmap
  constructor<;> intro H
  · specialize H Set.univ (Topology.isOpen_univ); simp at H
    apply H
  · intro U HU
    rw [Subtopology.isOpen_eq] at HU
    rcases HU with ⟨V, HV, rfl⟩
    have : Subtype.val '' {x : A | ↑x ∈ V} = A ∩ V := by ext x; simp; grind
    rw [this]
    apply Topology.isOpen_inter _ _ H HV

lemma Init.inverse_isSaturated  [HY : Topology Y] (f : X → Y) :
   ∀ U ∈ (Init.inverse f).isOpen, IsSaturated f U
:= by
  intro U HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨B, HB, rfl⟩
    intro x Hx y E; simp at *
    rw [<- E]; exact Hx
  | univ =>
    intro x Hx y E; simp at *
  | inter S T HS HT IHS IHT =>
    intro x ⟨Sx, Tx⟩ y E; simp at *
    have Sy := IHS x Sx y E
    have Ty := IHT x Tx y E
    grind
  | union S H IH =>
    intro x Hx y E; simp at *
    rcases Hx with ⟨s, Hs, xs⟩
    use s, Hs
    apply IH s Hs x xs; simp
    rw [E]

lemma IsOpenmap.ofSurjective  [HY : Topology Y] (f : X → Y) (Hf : f.Surjective) :
  IsOpenmap (HX := Init.inverse f) f
:= by
  intro U HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨B, HB, rfl⟩
    rw [Set.image_preimage_eq B Hf]
    exact HB
  | univ =>
    simp
    rw [Function.Surjective.range_eq Hf]
    apply Topology.isOpen_univ
  | inter S T HS HT IHS IHT =>
    have : f '' (S ∩ T) = (f '' S) ∩ (f '' T) := by {
      apply le_antisymm; apply Set.image_inter_subset
      intro x ⟨Sx, Tx⟩; simp at Sx Tx
      rcases Sx with ⟨s, Hs, Es⟩
      rcases Tx with ⟨t, Ht, Et⟩
      have E := Es.trans Et.symm
      have HS' := Init.inverse_isSaturated f S HS s Hs t E
      use t, ⟨HS', Ht⟩
    }
    rw [this]
    apply Topology.isOpen_inter _ _ IHS IHT
  | union S H IH =>
    rw [Set.image_sUnion]
    apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨y, Hy, rfl⟩
    apply IH y Hy


lemma prod.pr_openMap {I : Type _} (X : I → Type _) [HX : ∀ i, Topology (X i)] :
   ∀ i, IsOpenmap (prod.pr X i)
:= by
  intro i U HU
  rw [prod.pr_image_eq_sUnion]
  apply Topology.isOpen_sUnion
  intro s Hs; simp at Hs
  rcases Hs with ⟨g, Hg, rfl⟩
  have := prod.slice_isOpen g U HU i
  apply this


section

variable [HX : Topology X] [HY : Topology Y] [HZ : Topology Z]
variable (f : X → Y) (g : Y → Z)

lemma IsOpenmap_comp :
  IsOpenmap f → IsOpenmap g →  IsOpenmap (g ∘ f)
:= by
  intro Hf Hg U HU
  rw [Set.image_comp]
  apply Hg _ (Hf U HU)

lemma IsOpenmap_Surjective (Hf1 : f.Surjective) (Hf2 : IsContinuous f) :
  IsOpenmap (g ∘ f) → IsOpenmap g
:= by
  intro H U HU
  rw [<- Set.image_preimage_eq U Hf1, <- Set.image_comp]
  apply H
  rw [IsContinuous_iff] at Hf2
  apply Hf2 U HU

lemma IsOpenmap_Injective (Hg1 : g.Injective) (Hg2 : IsContinuous g) :
  IsOpenmap (g ∘ f) → IsOpenmap f
:= by
  intro H U HU
  rw [IsContinuous_iff] at Hg2
  rw [<- Set.preimage_image_eq (f '' U) Hg1]
  apply Hg2
  rw [<- Set.image_comp]
  apply H U HU


end

section


def codrest {X Y} (f : X → Y) (T : Set Y) : f ⁻¹' T → T := by
  apply Set.MapsTo.restrict f
  intro x; grind


variable [HX : Topology X] [HY : Topology Y] (f : X → Y) (T : Set Y)

lemma codrest_isOpenmap :
  IsOpenmap f → IsOpenmap (codrest f T)
:= by
  intro H U HU
  change U ∈ Topology.isOpen at HU
  rw [Subtopology.isOpen_eq] at HU ⊢
  rcases HU with ⟨V, HV, rfl⟩
  specialize H V HV
  use f '' V, H
  ext x; simp
  rcases x with ⟨x, Hx⟩
  simp [codrest, Set.MapsTo.restrict, Subtype.map]
  grind




variable {I : Type _} (T : I → Set Y)

lemma IsOpenmap_interior_covered (HT : ⋃ i, interior (T i) = Set.univ ) :
  (∀ i, IsOpenmap (codrest f (T i))) → IsOpenmap f
:= by
  intro H U HU
  change f '' U ∈ Topology.isOpen
  rw [Subtopology.isOpen_iff_covered_isOpen T HT (f '' U)]
  intro i; specialize H i
  unfold IsOpenmap at H
  have : {x : (f ⁻¹' T i) | x.val ∈ U} ∈ Topology.isOpen := by {
    rw [Subtopology.isOpen_eq]; simp
    use U, HU
  }
  apply H at this
  have E : {x : T i | x.val ∈ f '' U} = (codrest f (T i) '' {x | ↑x ∈ U}) := by {
    ext x; simp
    rcases x with ⟨x, Hx⟩
    simp [codrest, Set.MapsTo.restrict, Subtype.map]
    grind
  }
  rw [E]; exact this


lemma IsClosedmap_covered_closed
  (HT1 : LocallyFinite T)
  (HT2 : ⋃ i, T i = Set.univ)
  (HT3 : ∀ i, Topology.isClosed (T i)) :
  (∀ i, IsClosedmap (codrest f (T i))) → IsClosedmap f
:= by
  intro H U HU
  rw [Subtopology.isClosed_iff_covered_isClosed T HT1 HT2 HT3 (f '' U)]
  intro i; specialize H i
  unfold IsClosedmap at H
  have :  Topology.isClosed {x : (f ⁻¹' T i) | x.val ∈ U} := by {
    unfold Topology.isClosed
    change {x : (f ⁻¹' T i) | x.val ∈ U}ᶜ ∈ Topology.isOpen
    rw [Subtopology.isOpen_eq]; simp
    use Uᶜ, HU; ext x; simp
  }
  apply H at this
  have E : {x : T i | x.val ∈ f '' U} = (codrest f (T i) '' {x | ↑x ∈ U}) := by {
    ext x; simp
    rcases x with ⟨x, Hx⟩
    simp [codrest, Set.MapsTo.restrict, Subtype.map]
    grind
  }
  rw [E]; exact this
