import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous


namespace Bourbaki

/-
ブルバキ位の1.2.3逆位相での命題4の実装がLeanでは難しそう
調べたところ、MathlibでのTopologicalSpace.inducedが関連しそう
一旦、それを模して理解を深めてから、ブルバキに戻ろうかと思う
-/


#check TopologicalSpace.induced

def induced {X X'} (f : X → X') (HX' : Topology X') :
  Topology X
where
  isOpen U := ∃ U', HX'.isOpen U' ∧ U = f ⁻¹' U'
  isOpen_univ := by
    use Set.univ; simp; apply HX'.isOpen_univ
  isOpen_inter U V HU HV := by
    rcases HU with ⟨U', HU', rfl⟩
    rcases HV with ⟨V', HV', rfl⟩
    use U' ∩ V'; simp
    apply HX'.isOpen_inter<;> assumption
  isOpen_union S HS := by
    choose! g Hg1 Hg2 using HS
    use ⋃₀ {x | ∃ s, s ∈ S ∧ x = g s}; constructor
    · apply HX'.isOpen_union
      intro T; simp
      intro t Ht rfl
      apply Hg1 t Ht
    · ext x; simp
      constructor<;>
      intro ⟨s, Hs, H⟩<;>
      specialize Hg2 s Hs
      · rw [Hg2] at H; simp at H
        use s
      · use s, Hs; rw [Hg2]; simp; assumption

lemma induced_IsContinuous {X X'} (f : X → X') (HX' : Topology X') :
  @IsContinuous _ _ (induced f HX') HX' f
:= by
  rw [@IsContinuous_iff_IsOpen_preimage]
  intro U HU
  unfold Topology.isOpen induced; simp
  use U

lemma le_induced {X X'} (f : X → X') (HX' : Topology X')
  (HX : Topology X) (Hf : @IsContinuous _ _ HX HX' f) :
  HX ≤ induced f HX'
:= by
  simp [LE.le]
  intro U HU
  unfold Topology.isOpen induced at HU; simp at HU
  rcases HU with ⟨U', HU', rfl⟩
  rw [@IsContinuous_iff_IsOpen_preimage] at Hf
  apply Hf U' HU'


open Finset

example {Y : ι → Type _} [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :
  Topology X
:= by classical
  let 𝓖 := {V | ∃ i U, V = (f i) ⁻¹' U ∧ (HY i).isOpen U}
  let 𝓑 := {V : Set X | ∃ B : (Finset (Set X)), (B : Set (Set X)) ⊆  𝓖 ∧ V = ⋂₀ B}
  let 𝓓 := {V | ∃ B ⊆ 𝓑, V = ⋃₀ B}
  refine {
    isOpen U := U ∈ 𝓓
    isOpen_univ := by
      simp [𝓓, 𝓑, 𝓖]
      use {Set.univ}; simp
      use ∅; simp
    isOpen_inter := by
      intro x y Hx Hy
      simp [𝓓, 𝓑, 𝓖] at *
      rcases Hx with ⟨x', Hx', rfl⟩
      rcases Hy with ⟨y', Hy', rfl⟩
      have := Set.sUnion_inter_sUnion (s := x') (t := y')
      rw [<- Set.sUnion_image] at this
      use ((fun p ↦ p.1 ∩ p.2) '' x' ×ˢ y')
      constructor; swap; rw [this]
      intro S; simp
      intro a Ha b Hb E; subst S
      apply Hx' at Ha; simp at Ha
      apply Hy' at Hb; simp at Hb
      rcases Ha with ⟨a', Ha', rfl⟩
      rcases Hb with ⟨b', Hb', rfl⟩
      rw [<- Set.sInter_union]
      use a' ∪ b'; simp; constructor<;> assumption
    isOpen_union := by
      intro S H
      simp [𝓓] at *
      choose! g Hg using H
      use ⋃ s ∈ S, g s
      constructor
      · intro x Hx; simp at Hx
        rcases Hx with ⟨s, Hs, Hx⟩
        rcases Hg s Hs with ⟨Hgs, E⟩
        apply Hgs Hx
      · ext x; simp
        constructor<;> intro Hx
        · rcases Hx with ⟨s, Hs, xs⟩
          specialize Hg s Hs
          rcases Hg with ⟨Hgs, E⟩
          rw [E] at xs; simp at xs
          rcases xs with ⟨i, Hi, xi⟩
          use i, ?_, xi
          use s
        · rcases Hx with ⟨t, Ht, xt⟩
          rcases Ht with ⟨s, Hs, Ht⟩
          specialize Hg s Hs
          rcases Hg with ⟨Hgs, E⟩
          use s, Hs; rw [E]; simp
          use t, Ht, xt
  }








example [τ : Topology X]  {Y : ι → Type _}  [HY : ∀ i, Topology (Y i)]
  (f : ∀ i, X → Y i) (Hf : ∀ i, IsContinuous (f i)):
  TopologicalBase X
where
  base :=
    {V : Set X | ∃ B : (Finset (Set X)), (B : Set (Set X)) ⊆  {a | ∃ i U, a = (f i) ⁻¹' U ∧ (HY i).isOpen U} ∧ V = ⋂₀ B}
  base_isOpen := by
    intro V; simp
    intro B HB rfl
    apply isOpen_sInter
    intro b Hb; apply HB at Hb; simp at Hb
    rcases Hb with ⟨i, U, rfl, HU⟩
    specialize Hf i
    rw [@IsContinuous_iff_IsOpen_preimage] at Hf
    apply Hf _ HU
  covered := by
    intro U HU
