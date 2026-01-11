import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor

namespace Bourbaki

def TopologicalBase.topology [HX : Topology X] (𝓑 : TopologicalBase X) :
  Topology X
where
  isOpen U := ∃ B ⊆ 𝓑.base, U = ⋃₀ B
  isOpen_univ := by
    have ⟨B, HB, E⟩ := @𝓑.covered Set.univ HX.isOpen_univ
    use B
  isOpen_inter S T := by
    intro ⟨S', HS', ES⟩ ⟨T', HT', ET⟩
    rw [ES, ET]; clear ES ET
    have HUS : ⋃₀ S' ∈ HX.isOpen := by {
      apply HX.isOpen_union
      intro s Hs; apply HS' at Hs
      apply 𝓑.base_isOpen Hs
    }
    have HUT : ⋃₀ T' ∈ HX.isOpen := by {
      apply HX.isOpen_union
      intro t Ht; apply HT' at Ht
      apply 𝓑.base_isOpen Ht
    }
    have HST := HX.isOpen_inter _ _ HUS HUT
    rcases 𝓑.covered _ HST with ⟨U, HU, E⟩
    rw [E]; use U
  isOpen_union S HS := by
    choose! f Hf Hf' using HS
    let B := ⋃₀ {V | ∃ s ∈ S, V = f s}
    use ⋃₀ {V | ∃ s ∈ S, V = f s}
    constructor
    · intro T HT; simp at HT
      rcases HT with ⟨s, Hs, Ts⟩
      apply Hf s Hs Ts
    · ext x; simp
      constructor<;> intro Hx
      · rcases Hx with ⟨s, Hs, xs⟩
        have E := Hf' s Hs
        rw [E] at xs; simp at xs
        rcases xs with ⟨t, Ht, xt⟩
        use t, ?_, xt
        use s
      · rcases Hx with ⟨t, ⟨s, Hs, H⟩, Ht⟩
        have E := Hf' s Hs
        use s, Hs; rw [E]; simp
        use t

lemma TopologicalBase.topology_eq [HX : Topology X] (𝓑 : TopologicalBase X) :
  𝓑.topology = HX
:= by
  ext U; simp [topology]
  conv => arg 1; change ∃ B ⊆ 𝓑.base, U = ⋃₀ B
  constructor<;> intro HU
  · rcases HU with ⟨B, HB, rfl⟩
    apply HX.isOpen_union
    intro b Hb
    apply 𝓑.base_isOpen
    apply HB Hb
  · apply 𝓑.covered _ HU

def IsTopologicalSubbase [HX : Topology X] (B : Set (Set X)) :=
  IsTopologicalBase {V : Set X | ∃ U : (Finset (Set X)), (U : Set (Set X)) ⊆ B   ∧ V = ⋂₀ U}

inductive SubbasisOpen (B : Set (Set X)) : (Set X) → Prop
  | base U : U ∈ B → SubbasisOpen B U
  | univ : SubbasisOpen B Set.univ
  | inter S T : SubbasisOpen B S → SubbasisOpen B T → SubbasisOpen B (S ∩ T)
  | union S : (∀ s ∈ S, SubbasisOpen B s) → SubbasisOpen B (⋃₀ S)

instance Subbase_topology (B : Set (Set X)) :
  Topology X
where
  isOpen U := SubbasisOpen B U
  isOpen_univ := SubbasisOpen.univ
  isOpen_inter S T HS HT := SubbasisOpen.inter S T HS HT
  isOpen_union S HS := by apply SubbasisOpen.union S; grind

example [HX : Topology X] {B : Set (Set X)} (HB : IsTopologicalSubbase B) U :
  U ∈ HB.topologicalBase.topology.isOpen ↔  (Subbase_topology B).isOpen U
:= by
  simp [TopologicalBase.topology]
  simp [IsTopologicalBase.topologicalBase]
  simp [Subbase_topology]
  constructor<;> intro H
  · rcases H with ⟨V, HV, rfl⟩
    apply SubbasisOpen.union
    intro v Hv; apply HV at Hv; simp at Hv
    rcases Hv with ⟨W, WV, rfl⟩
    induction W using Finset.cons_induction_on with
    | empty =>
      simp; apply SubbasisOpen.univ
    | cons S B' F IH =>
      simp; apply SubbasisOpen.inter; swap
      · grind
      · apply SubbasisOpen.base
        grind
  · induction H with
    | base V HV =>
      have : V ∈ HX.isOpen := by {
        apply HB.topologicalBase.base_isOpen
        simp [IsTopologicalBase.topologicalBase]
        use {V}; simp; assumption
      }
      have ⟨W, HW, E⟩ := HB.topologicalBase.covered _ this
      simp [IsTopologicalBase.topologicalBase] at HW
      rw [E]
      use W
    | univ =>
      have := HB.topologicalBase.covered _ HX.isOpen_univ
      simp [IsTopologicalBase.topologicalBase] at this
      rcases this with ⟨V, HV, E⟩; rw [E]; clear E
      use V
    | inter S T HS HT IHS IHT =>
      rcases IHS with ⟨S', HS', ES⟩
      rcases IHT with ⟨T', HT', ET⟩
      rw [ES, ET]; clear ES ET
      have H1 : ⋃₀ S' ∈ HX.isOpen := by {
        apply HX.isOpen_union
        intro s Hs; apply HS' at Hs; simp at Hs
        apply HB.topologicalBase.base_isOpen
        simp [IsTopologicalBase.topologicalBase]
        exact Hs
      }
      have H2 : ⋃₀ T' ∈ HX.isOpen := by {
        apply HX.isOpen_union
        intro t Ht; apply HT' at Ht; simp at Ht
        apply HB.topologicalBase.base_isOpen
        simp [IsTopologicalBase.topologicalBase]
        exact Ht
      }
      have HST := HX.isOpen_inter _ _ H1 H2
      rcases HB.topologicalBase.covered _ HST with ⟨U, HU, E⟩
      simp [IsTopologicalBase.topologicalBase] at HU
      rw [E]; use U
    | union S HS IH =>
      choose! f Hf1 Hf2 using IH
      use ⋃₀ {V | ∃ s ∈ S, V = f s}
      constructor; swap
      · ext x; simp
        constructor<;> intro Hx
        · rcases Hx with ⟨s, Hs, xs⟩
          have E := Hf2 s Hs
          rw [E] at xs; simp at xs
          rcases xs with ⟨t, Ht, xt⟩
          use t, ?_, xt
          use s
        · rcases Hx with ⟨t, ⟨s, Hs, H⟩, Ht⟩
          have E := Hf2 s Hs
          use s, Hs; rw [E]; simp
          use t
      · intro T HT; simp at HT; simp
        rcases HT with ⟨s, Hs, HT⟩
        specialize Hf1 s Hs HT; simp at Hf1
        exact Hf1

end Bourbaki
