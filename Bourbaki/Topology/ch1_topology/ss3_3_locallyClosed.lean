import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace
import Bourbaki.Topology.ch1_topology.ss3_2_continuous
import Mathlib.Tactic.TFAE

namespace Bourbaki

def IsLocallyClosed [HX : Topology X] (L : Set X) :=
  ∃ U V, HX.isOpen U ∧ HX.isClosed V ∧ L = U ∩ V

/-
  4 ↔ 3
  ↓  ↖
  1 → 2
  ↑ ↙
  5

  5 → 3
-/
lemma isLocallyClosed_tfae [HX : Topology X] (L : Set X) :
    List.TFAE
    [ IsLocallyClosed L,
      HX.isClosed (closure L ∩ Lᶜ),
      ∀ x ∈ L, ∃ U ∈ neighborOf x, Topology.isClosed ({x : U | x.val ∈ L}),
      ∀ x ∈ L, ∃ U, x ∈ U ∧ HX.isOpen U ∧ U ∩ closure L ⊆ L,
      {x : closure L | x.val ∈ L} ∈ Topology.isOpen ]
:= by classical
  unfold IsLocallyClosed



  tfae_have 1 → 2 := by {
    intro ⟨U, V, HU, HV, E⟩
    unfold Topology.isClosed
    rw [coborder_eq_union_frontier_compl]
    nth_rw 1 [E]
    rw [Set.inter_union_distrib_right]
    apply HX.isOpen_inter
    · apply HX.isOpen_union _ _ HU
      apply frontier_isCloses
    · suffices : V ∪ (frontier L)ᶜ = Set.univ; rw [this]; apply HX.isOpen_univ
      ext x; simp
      by_contra F; simp at F; rcases F with ⟨Fx, Hx⟩
      apply Fx; clear Fx
      rw [mem_frontier_iff] at Hx
      by_contra Fx : x ∈ Vᶜ
      have := mem_neighbor_iff_isOpen.mpr HV x Fx
      apply Hx at this
      rcases this with ⟨F1, F2⟩
      apply F1; ext i; simp
      rw [E]; simp
  }

  tfae_have 2 → 4 := by{
    intro H l Hl
    unfold Topology.isClosed at H
    have H' := mem_neighbor_iff_isOpen.mpr H
    have : l ∈ (closure L ∩ Lᶜ)ᶜ := by grind
    specialize H' l this
    use (closure L ∩ Lᶜ)ᶜ, this, H
    rw [Set.compl_inter]; simp
    rw [Set.union_inter_distrib_right]; simp
  }



  tfae_have 4 → 1 := by {
    intro H
    choose! f Hf1 Hf2 Hf3 using H
    let U := ⋃ l ∈ L, f l
    have HU : HX.isOpen U := by {
      apply HX.isOpen_sUnion
      intro l Hl; simp at Hl
      rcases Hl with ⟨y, rfl⟩
      apply HX.isOpen_sUnion
      intro l Hl; simp at Hl
      rcases Hl with ⟨Ly, rfl⟩
      apply Hf2 y Ly
    }
    use U, closure L, HU, closure_isClosed L
    simp [U]
    ext x; simp; constructor<;> intro Hx
    · constructor
      · use x, Hx, Hf1 x Hx
      · apply le_closure L Hx
    · rcases Hx with ⟨⟨l, Hl, Hfl⟩, Hx⟩
      apply Hf3 l Hl; grind

  }

  tfae_have 2 → 5 := by {
    intro H
    unfold Topology.isClosed at H
    rw [Set.compl_inter] at H; simp at H
    rw [Subtopology.isOpen_eq]; simp
    use ((closure L)ᶜ ∪ L), H
    ext x; simp
  }

  tfae_have 5 → 1 := by {
    intro H
    rw [Subtopology.isOpen_eq] at H; simp at H
    rcases H with ⟨U, HU, E⟩
    change Subtype.val ⁻¹' L = Subtype.val ⁻¹' U at E
    rw [Subtype.preimage_val_eq_preimage_val_iff] at E
    have := le_closure L
    rw [<- Set.inter_eq_right] at this
    rw [this, Set.inter_comm] at E; clear this
    use U, closure L, HU, closure_isClosed L, E
  }

  tfae_have 3 → 4 := by {
    intro H l Hl
    rcases H l Hl with ⟨U, HU, E⟩
    rw [Subtopology.isClosed_iff] at E
    rcases E with ⟨V, HV, E⟩
    change Subtype.val ⁻¹' L = Subtype.val ⁻¹' V at E
    rw [Subtype.preimage_val_eq_preimage_val_iff] at E
    unfold neighborOf NeighborOf at HU; simp at HU
    rcases HU with ⟨W, HW, Wl, WU⟩
    have EW : W ∩ L = W ∩ V := by {
      ext x; constructor<;> intro ⟨Hx1, Hx2⟩
      · have : x ∈ U ∩ L := by grind
        rw [E] at this; grind
      · have : x ∈ U ∩ V := by grind
        rw [<- E] at this; grind
    }
    use W, Wl, HW
    intro x Hx
    have := HW.closure_inter  L Hx
    rw [EW] at this
    apply closure_inter at this
    rw [isClosed_iff_eq_closure.mp HV] at this
    rcases this with ⟨Wx', Vx⟩
    rcases Hx with ⟨Wx, Lx'⟩
    have : x ∈ W ∩ L := by grind
    grind
  }

  tfae_have 4 → 3 := by {
    intro H l Hl
    rcases H l Hl with ⟨U, Ul, HU, HUL⟩
    have H := mem_neighbor_iff_isOpen.mpr HU l Ul
    use U, H
    rw [Subtopology.isClosed_iff]
    use closure L, closure_isClosed L
    ext x; simp
    constructor<;> intro Hx
    · apply le_closure L Hx
    · apply HUL; simp; grind
  }

  -- tfae_have 5 → 3 := by {
  --   intro H l Hl
  --   rw [Subtopology.isOpen_eq] at H; simp at H
  --   rcases H with ⟨U, HU, E⟩
  --   change Subtype.val ⁻¹' L = Subtype.val ⁻¹' U at E
  --   rw [Subtype.preimage_val_eq_preimage_val_iff] at E
  --   have := le_closure L
  --   rw [<- Set.inter_eq_right] at this
  --   rw [this, Set.inter_comm] at E; clear this
  --   rw [E] at Hl; simp at Hl
  --   rcases Hl with ⟨Ul, Hl⟩
  --   use U, mem_neighbor_iff_isOpen.mpr HU l Ul
  --   rw [Subtopology.isClosed_iff]
  --   use closure L, closure_isClosed L
  --   ext x; simp
  --   rcases x with ⟨x, Ux⟩; simp
  --   constructor<;> intro Hx
  --   · apply le_closure L Hx
  --   · rw [E]; simp; grind
  -- }

  tfae_finish
