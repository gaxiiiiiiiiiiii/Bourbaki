import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor

namespace Bourbaki


def IsContinuousAt [Topology X] [Topology X'] (f : X → X') (x₀ : X) :=
  ∀ V' ∈ neighborOf (f x₀), f ⁻¹' V' ∈ neighborOf x₀

lemma IsContinuousAt_iff [Topology X] [Topology X'] (f : X → X') (x₀ : X) :
  IsContinuousAt f x₀ ↔ (∀ V' ∈ neighborOf (f x₀), ∃ V ∈ neighborOf x₀, ∀ x ∈ V, f x ∈ V')
:= by
  simp [IsContinuousAt]
  constructor<;> intro H V' HV'<;> specialize H V' HV'; swap
  · rcases H with ⟨V, HV, H⟩
    simp [neighborOf, NeighborOf] at HV ⊢
    rcases HV with ⟨U, HU, Ux, UV⟩
    use U, HU, Ux
    intro y Uy; simp
    apply H; apply UV Uy
  · use f ⁻¹' V', H; simp

lemma IsContinuousAt_iff_closure [Topology X] [Topology X'] (f : X → X') (x : X) :
  IsContinuousAt f x ↔ ∀ A, x ∈ closure A → f x ∈ closure (f '' A)
:= by
  constructor
  unfold IsContinuousAt
  · intro Hf A HA
    by_contra F : f x ∈ (closure (f '' A))ᶜ
    rw [compl_closure, mem_interior_iff_neighborOf] at F
    apply Hf at F; simp at F
    rw [<- mem_interior_iff_neighborOf, <- compl_closure] at F
    apply F; clear F Hf
    revert HA x
    change closure A ⊆ _
    apply closure_mono
    intro x Hx; simp; use x
  . intro H B HB
    rw [<- mem_interior_iff_neighborOf, <- compl_compl B, <- compl_closure] at HB
    rw [<- mem_interior_iff_neighborOf]
    by_contra (F : x ∈ (interior (f ⁻¹' B))ᶜ)
    rw [compl_interior] at F
    specialize H _ F
    clear F
    apply HB
    have : closure (f '' (f ⁻¹' B)ᶜ) ⊆ closure Bᶜ := by {
      apply closure_mono; simp
    }
    apply this H

lemma IsContinuousAt_comp [Topology X] [Topology X'] [Topology X''] {f : X → X'} {g : X' → X''}
  (x₀ : X) (Hf : IsContinuousAt f x₀) (Hg : IsContinuousAt g (f x₀)) :
  IsContinuousAt (g ∘ f) x₀
:= by
  simp [IsContinuousAt] at *
  intro V'' HV''
  specialize Hg _ HV''
  specialize Hf _ Hg
  rw [Set.preimage_comp]
  exact Hf

def IsContinuous [Topology X] [Topology X'] (f : X → X') :=
  ∀ x , IsContinuousAt f x

lemma IsContinuous_iff_subset [Topology X] [Topology X'] (f : X → X') :
  IsContinuous f ↔ ∀ A , f '' (closure A) ⊆ closure (f '' A)
:= by
  simp [IsContinuous, IsContinuousAt_iff_closure]
  grind

lemma IsContinuous_iff_IsClosed_preimage [HX : Topology X] [HX' : Topology X'] (f : X → X') :
  IsContinuous f  ↔ ∀ V', HX'.isClosed V' → HX.isClosed (f ⁻¹' V')
:= by
  rw [IsContinuous_iff_subset]
  constructor<;> intro H
  ·
    intro V' HV'
    have H' := H (f ⁻¹' V')
    rw [isClosed_iff_eq_closure] at ⊢ HV'
    ext x; simp
    constructor<;> intro Hx
    · have Hfx : f x ∈ f '' (closure (f ⁻¹' V')) := by grind
      apply H at Hfx
      rw [<- HV']
      have : closure (f '' (f ⁻¹' V')) ⊆ closure V' := by  apply closure_mono; simp
      apply this; assumption
    · rw [mem_closure_iff]
      intro U HU F
      have Ux := neighborOf_mem_self HU
      have Hx' : x ∈ (f ⁻¹' V')ᶜ := by intro F; have : x ∈ f ⁻¹' V' ∩ U := by {grind}; grind
      apply Hx'; simp
      assumption
  · intro A x' ⟨x, Hx, E⟩; subst x'
    specialize H (closure (f '' A)) (closure_isClosed _)
    rw [isClosed_iff_eq_closure] at H
    suffices : x ∈ f⁻¹' (closure (f '' A)); grind
    rw [<- H]
    clear H -- ???
    revert x Hx
    change closure A ⊆ closure (f ⁻¹' closure (f '' A))
    apply closure_mono
    intro x Hx; simp
    rw [mem_closure_iff]
    intro U HU F
    have : f x ∈ f '' A ∩ U := by {
      simp; constructor; use x
      apply neighborOf_mem_self HU
    }
    grind

lemma IsContinuous_iff [HX : Topology X] [HX' : Topology X'] (f : X → X') :
  IsContinuous f  ↔ ∀ V', HX'.isOpen V' → HX.isOpen (f ⁻¹' V')
:= by
  rw [IsContinuous_iff_IsClosed_preimage]
  constructor<;> intro H V' HV'
  · have := H V'ᶜ (by simp [Topology.isClosed]; grind)
    simp [Topology.isClosed] at this
    exact this
  · have := H V'ᶜ HV'
    simp [Topology.isClosed]
    rw [<- Set.preimage_compl]
    exact this

lemma IsContinuous_iff_base [HX : Topology X] [HX' : Topology X'] (f : X → X') (𝓑 : TopologicalBase X') :
  IsContinuous f ↔ ∀ U' ∈ 𝓑.base, HX.isOpen (f ⁻¹' U')
:= by
  rw [IsContinuous_iff]
  constructor<;> intro H
  · intro U' HU'
    apply H U' (𝓑.base_isOpen HU')
  · intro U HU
    have ⟨B, HB, E⟩ := 𝓑.covered U HU
    subst U; simp
    have : (⋃ t ∈ B, f ⁻¹' t) = ⋃₀ ((λ t : Set X' => f ⁻¹' t) '' B)  := by simp
    rw [this]; clear this
    apply HX.isOpen_sUnion
    simp; intro b Hb
    apply H; apply HB Hb

lemma IsContinuous_comp [Topology X] [Topology X'] [Topology X''] {f : X → X'} {g : X' → X''}
  (Hf : IsContinuous f) (Hg : IsContinuous g) :
  IsContinuous (g ∘ f)
:= by
  intro s; apply IsContinuousAt_comp; apply Hf; apply Hg


lemma Homeomorphic_iff_continuous [Topology X] [Topology X'] :
  Nonempty (Homeomorphic X X') ↔ ∃ f : X ≃ X', IsContinuous f.toFun ∧ IsContinuous f.invFun
:= by
  constructor
  · intro ⟨f⟩
    use f.toEquiv
    have H := f.continuous_fun
    have H' := f.continuous_inv
    constructor<;> rw [IsContinuous_iff]<;> assumption
  . intro ⟨E, H1, H2⟩
    rw [IsContinuous_iff] at H1 H2
    constructor; use E

structure IsHomeomorphic [Topology X] [Topology X'] (f : X → X') where
  continuous : IsContinuous f
  bij :  f.Bijective
  open_map : ∀ x U, U ∈ neighborOf x → f '' U ∈ neighborOf (f x)


noncomputable def IsHomeomorphic.Homeomorphic [Topology X] [Topology X'] {f : X → X'} (H : IsHomeomorphic f) :
  Homeomorphic X X'
:= by
  let E := Equiv.ofBijective _ H.bij
  have Hf := H.continuous
  have H2 := H.open_map
  apply Homeomorphic.mk E
  · intro S HS
    conv => arg 1; arg 1; change f
    rw [IsContinuous_iff] at Hf
    apply Hf S HS
  · intro S HS
    rw [<- mem_neighbor_iff_isOpen] at HS ⊢
    intro x Hx; simp at Hx
    unfold IsContinuous IsContinuousAt at Hf
    let g := E.invFun
    change g x ∈ S at Hx
    have Hfg := E.right_inv x
    change f (g x) = x at Hfg
    have H3 := H2 (g x) S (HS _ Hx)
    rw [Hfg] at H3
    apply neighborOf_subset H3
    intro x; simp
    intro y Hy E; subst x
    change g (f y) ∈ S
    have H := E.left_inv y
    change g (f y) = y at H
    rw [H]
    exact Hy

def Homeomorphic.isHomeomorphic [Topology X] [Topology X'] (E : Homeomorphic X X') :
  IsHomeomorphic E.toFun
:= by
  have H1 := E.continuous_fun
  have H2 := E.bijective
  have H3 := E.continuous_inv
  rw [<- IsContinuous_iff] at H1
  use H1, H2
  intro x U HU
  set f := E.toFun
  set g := E.invFun
  simp [neighborOf, NeighborOf] at HU ⊢
  rcases HU with ⟨V, HV, Vx, UV⟩
  specialize H3 V HV
  use (g ⁻¹' V), H3; simp
  have : g (f x) = x := E.left_inv x
  rw [this]
  use Vx
  intro y; simp
  intro Hy
  apply UV at Hy
  use g y, Hy
  have : f (g y) = y := E.right_inv y
  rw [this]

example [HX : Topology X] (x₀ : X) :
  NeighborClass X
where
  neighbor x := {U | (x = x₀ ∧ U ∈ neighborOf x₀) ∨ (x ≠ x₀ ∧ x ∈ U)}
  nonempty := by
    intro x
    by_cases H : x = x₀
    · subst x₀; simp
      apply neighborOf_notempty
    · use {x}; simp; right; exact H
  inter x V W HV HW := by
    simp at HV HW ⊢
    rcases HV with ⟨E, HV⟩ | ⟨F, HV⟩<;>
    rcases HW with ⟨E', HW⟩ | ⟨F, HW⟩<;>
    try contradiction
    · left; use E; apply neighborOf_inter HV HW
    · right; use F
  mem_self := by
    intro x; simp
    intro U HU
    rcases HU with ⟨E, HU⟩ | ⟨F, HU⟩; swap; assumption
    subst x₀
    apply neighborOf_mem_self HU
  core := by
    intro x U; simp; intro HU
    rcases HU with ⟨E, HU⟩ | ⟨F, HU⟩
    · subst x₀; simp
      use U, HU
      intro y Hy
      by_cases E : y = x
      · subst y; simp; assumption
      · right; use E
    · use {x}; constructor
      · right; use F; simp
      · simp; right; use F, HU
  subset x V W  HV VW := by
    simp at HV ⊢
    rcases HV with ⟨E, HV⟩ | ⟨F, HV⟩
    · left; use E
      apply neighborOf_subset HV VW
    · right; use F
      apply VW HV

instance {X} : PartialOrder (Topology X) where
  le HX HX' := ∀ U, HX'.isOpen U → HX.isOpen U
  le_refl _ _ := by simp
  le_trans a b c H1 H2 := by grind
  le_antisymm a b H1 H2 := by ext x; exact ⟨H2 x, H1 x⟩

lemma Topology_le_iff_isOpen (s t : Topology X) :
  s ≤ t ↔ (∀ U , t.isOpen U → s.isOpen U)
:= by simp [LE.le]

lemma Topology_le_iff_closure (s t : Topology X) :
  s ≤ t ↔ (∀ U , @closure _ s U ⊆ @closure _ t U)
:= by
  simp [LE.le]
  have E := @IsContinuous_iff_subset _ _ s t id; simp at E
  rw [@IsContinuous_iff] at E; simp at E
  exact E

lemma Topology_le_iff_neighbor (s t : Topology X) :
  s ≤ t ↔ (∀ x U, U ∈ @neighborOf _ t x → U ∈ @neighborOf _ s x)
:= by
  conv => arg 2; change @IsContinuous _ _ s t id
  simp [LE.le]
  rw [@IsContinuous_iff]; simp

lemma Topology_le_iff_isClosed (s t : Topology X) :
  s ≤ t ↔ (∀ U , t.isClosed U → s.isClosed U)
:= by
  simp [LE.le]
  have E := @IsContinuous_iff_IsClosed_preimage _ _ s t id; simp at E
  rw [@IsContinuous_iff] at E; simp at E
  exact E

instance {X} : OrderBot (Topology X) where
  bot := {
    isOpen S := S ∈ Set.univ
    isOpen_univ := by simp;
    isOpen_inter := by simp
    isOpen_sUnion := by simp
  }
  bot_le x := by simp [LE.le]

instance {X} : OrderTop (Topology X) where
  top := {
    isOpen S := S = ∅ ∨ S = Set.univ
    isOpen_univ := by simp
    isOpen_inter := by
      intro x y Hx Hy
      rcases Hx with ⟨Hx⟩<;>
      rcases Hy with ⟨Hy⟩<;>
      try subst x y; simp
    isOpen_sUnion := by
      intro S HS
      by_contra F; simp at F; rcases F with ⟨F1, F2⟩
      rcases F1 with ⟨s, Hs, Fs⟩
      rcases HS s Hs with H | H; contradiction
      apply F2; ext i; simp
      subst s
      use Set.univ, Hs; simp
  }
  le_top x := by
    simp [LE.le]
    constructor
    · apply Topology.isOpen_empty
    · apply Topology.isOpen_univ


lemma le_com_continuous (HX HX' : Topology X) [Topology Y ] (f : X → Y) (Hf : @IsContinuous _ _ HX HY f) :
  HX' ≤ HX → @IsContinuous _ _ HX' HY f
:= by
  simp [LE.le]
  intro H
  rw [@IsContinuous_iff] at Hf ⊢
  intro U HU
  specialize Hf U HU
  apply  H _ Hf

lemma cod_le_continuous [Topology X] (HY HY' : Topology Y)  (f : X → Y)
  (H : HY ≤ HY') (Hf : @IsContinuous _ _ HX HY f) :
  @IsContinuous _ _ HX HY' f
:= by
  simp [LE.le] at H
  rw [@IsContinuous_iff] at Hf ⊢
  intro U HU
  specialize H U HU
  apply Hf _ H


-- def inverse  {Y : ι → Type _} [HY : ∀ i, Topology (Y i)]  (f : ∀ i, X → Y i) :
--   Topology X
-- := by classical
--   let 𝓖 := {V | ∃ i U, V = (f i) ⁻¹' U ∧ (HY i).isOpen U}
--   let 𝓑 := {V : Set X | ∃ B : (Finset (Set X)), (B : Set (Set X)) ⊆  𝓖 ∧ V = ⋂₀ B}
--   let 𝓓 := {V | ∃ B ⊆ 𝓑, V = ⋃₀ B}
--   refine {
--     isOpen U := U ∈ 𝓓
--     isOpen_univ := by
--       simp [𝓓, 𝓑, 𝓖]
--       use {Set.univ}; simp
--       use ∅; simp
--     isOpen_inter := by
--       intro x y Hx Hy
--       simp [𝓓, 𝓑, 𝓖] at *
--       rcases Hx with ⟨x', Hx', rfl⟩
--       rcases Hy with ⟨y', Hy', rfl⟩
--       have := Set.sUnion_inter_sUnion (s := x') (t := y')
--       rw [<- Set.sUnion_image] at this
--       use ((fun p ↦ p.1 ∩ p.2) '' x' ×ˢ y')
--       constructor; swap; rw [this]
--       intro S; simp
--       intro a Ha b Hb E; subst S
--       apply Hx' at Ha; simp at Ha
--       apply Hy' at Hb; simp at Hb
--       rcases Ha with ⟨a', Ha', rfl⟩
--       rcases Hb with ⟨b', Hb', rfl⟩
--       rw [<- Set.sInter_union]
--       use a' ∪ b'; simp; constructor<;> assumption
--     isOpen_sUnion := by
--       intro S H
--       simp [𝓓] at *
--       choose! g Hg using H
--       use ⋃ s ∈ S, g s
--       constructor
--       · intro x Hx; simp at Hx
--         rcases Hx with ⟨s, Hs, Hx⟩
--         rcases Hg s Hs with ⟨Hgs, E⟩
--         apply Hgs Hx
--       · ext x; simp
--         constructor<;> intro Hx
--         · rcases Hx with ⟨s, Hs, xs⟩
--           specialize Hg s Hs
--           rcases Hg with ⟨Hgs, E⟩
--           rw [E] at xs; simp at xs
--           rcases xs with ⟨i, Hi, xi⟩
--           use i, ?_, xi
--           use s
--         · rcases Hx with ⟨t, Ht, xt⟩
--           rcases Ht with ⟨s, Hs, Ht⟩
--           specialize Hg s Hs
--           rcases Hg with ⟨Hgs, E⟩
--           use s, Hs; rw [E]; simp
--           use t, Ht, xt
--   }


-- def inverseBase {Y : ι → Type _} [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :
--   @TopologicalBase X (inverse f)
-- := by
--   apply @TopologicalBase.mk X (inverse f)
--   case base => exact {V : Set X | ∃ B : (Finset (Set X)), (B : Set (Set X)) ⊆  {V | ∃ i U, V = (f i) ⁻¹' U ∧ (HY i).isOpen U} ∧ V = ⋂₀ B}
--   case base_isOpen =>
--     intro x Hx; simp at Hx
--     unfold Topology.isOpen inverse; simp
--     rcases Hx with ⟨B, HB, rfl⟩
--     use {⋂₀ B}; simp
--     use B
--   case covered =>
--     intro U HU
--     unfold Topology.isOpen inverse at HU; simp at HU
--     rcases HU with ⟨B, HB, rfl⟩
--     use B

-- lemma le_inverse {Y : ι → Type _} [HY : ∀ i, Topology (Y i)]  (f : ∀ i, X → Y i) (HX : Topology X) :
--   (∀ i, IsContinuous (f i)) → HX ≤ inverse f
-- := by
--   intro H; simp [LE.le]
--   intro U HU
--   simp [inverse] at HU
--   rcases HU with ⟨B, HB, rfl⟩
--   apply HX.isOpen_sUnion
--   intro b Hb
--   apply HB at Hb; simp at Hb
--   rcases Hb with ⟨C, HC, rfl⟩
--   apply isOpen_sInter
--   intro c Hc; apply HC at Hc; simp at Hc
--   rcases Hc with ⟨i, U, rfl, HU⟩
--   specialize H i
--   rw [@IsContinuous_iff] at H
--   apply H _ HU

-- lemma IsContinuous_inverse {Y : ι → Type _} [HY : ∀ i, Topology (Y i)]  (f : ∀ i, X → Y i) (i : ι):
--   @IsContinuous _ _ (inverse f) _ (f i)
-- := by
--   rw [@IsContinuous_iff]
--   intro U HU; simp [inverse]
--   use {f i ⁻¹' U}; simp
--   use {f i ⁻¹' U}; simp
--   use i, U


-- lemma IsContinuous_inverse_iff [DecidableEq (Set Z)] {Y : ι → Type _} [HY : ∀ i, Topology (Y i)] [Topology Z]  (f : ∀ i, X → Y i) (g : Z → X) :
--   ( @IsContinuous Z X _ (inverse f) g) ↔ ∀ i, IsContinuous (f i ∘ g)
-- := by
--   constructor<;> intro H
--   · intro i z S HS; simp at HS
--     rw [Set.preimage_comp]; apply H
--     let B := inverseBase f
--     simp [neighborOf, NeighborOf] at *
--     rcases HS with ⟨U, HU, Hfg, US⟩
--     use f i ⁻¹' U; constructor; swap
--     · simp; use Hfg
--       apply Set.preimage_mono US
--     · simp [inverse]
--       use {f i ⁻¹' U}; simp
--       use {f i ⁻¹' U}; simp
--       use i, U
--   · intro z S HS
--     simp [neighborOf, NeighborOf] at HS
--     rcases HS with ⟨U, HU, Hfg, US⟩
--     simp [inverse] at HU
--     rcases HU with ⟨B, HB, rfl⟩
--     simp at *
--     rcases Hfg with ⟨b, Hb, Hgb⟩
--     have bS := US b Hb
--     apply HB at Hb; simp at Hb
--     rcases Hb with ⟨C, HC, rfl⟩
--     simp at *

--     clear HB US

--     use (g ⁻¹' ⋂₀ ↑C); constructor; swap; constructor
--     · simp; assumption
--     · apply Set.preimage_mono bS
--     · have :  (g ⁻¹' ⋂₀ ↑C) = ⋂₀ (Finset.image (fun c => g ⁻¹' c) C) := by simp
--       rw [this]; clear this
--       apply isOpen_sInter
--       intro z' Hz'; simp at Hz'
--       rcases Hz' with ⟨c, Hc, rfl⟩
--       specialize Hgb c Hc
--       specialize HC Hc; simp at HC
--       rcases HC with ⟨i, U, rfl, HU⟩; simp at *

--       rw [<- mem_neighbor_iff_isOpen]
--       intro x Hx; simp at Hx
--       rw [<- mem_neighbor_iff_isOpen] at HU
--       apply HU at Hx
--       specialize H i x U Hx
--       exact H

end Bourbaki
