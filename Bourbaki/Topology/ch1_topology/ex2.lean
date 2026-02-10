import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2

namespace Bourbaki

section ex_2_1

variable [Topology X] [Topology X'] (f : X → X')
#check interior
example :
  IsContinuous f ↔ ∀ A' : Set X', f ⁻¹' (interior A') ⊆ interior (f ⁻¹' A')
:= by
  constructor<;> intro H
  · rw [IsContinuous_iff] at H
    intro A' x Hx
    simp [interior] at Hx ⊢
    rcases Hx with ⟨U', ⟨HU', UA⟩, U'x⟩
    apply H at HU'
    use f⁻¹' U', ⟨HU', ?_⟩<;> grind
  · rw [IsContinuous_iff_subset]
    intro U
    rw [<- Set.compl_subset_compl, compl_closure]
    intro x' Hx' Fx'
    simp at Fx'
    rcases Fx' with ⟨x, Hx, rfl⟩
    rw [<- Set.mem_preimage] at Hx'
    apply H at Hx'
    rw [Set.preimage_compl, <- compl_closure] at Hx'
    apply Hx'; clear Hx'
    have := Set.subset_preimage_image f U
    apply closure_mono at this
    apply this Hx

example A' :
  f ⁻¹' (interior A') ⊆ interior (f ⁻¹' A') ↔ closure (f ⁻¹' A'ᶜ) ⊆ f ⁻¹' (closure A'ᶜ)
:= by
  conv => arg 1; rw [<- Set.compl_subset_compl]
  rw [compl_interior, <- Set.preimage_compl, <- Set.preimage_compl, compl_interior]

end ex_2_1

section ex_2_3

example [HX : Topology X] [HX' : Topology X'] (f : X → X') (Hf : f.Bijective) :
  IsHomeomorphic f ↔ HX = Init.induced (Function.Embedding.mk f Hf.injective)
:= by
  constructor<;> intro H
  · apply le_antisymm
    · unfold Init.induced
      rw [<- Init.IsContinuous_iff_le_inverse]
      simp
      exact H.continuous
    · intro U HU
      apply GenedOpen.base
      simp [Init.subbase, Init.to]
      use f '' U
      rw [propext (Set.eq_preimage_iff_image_eq Hf)]; simp
      change HX'.isOpen (f '' U)
      rw [<- mem_neighbor_iff_isOpen]
      intro x' Hx'; simp at Hx'
      rcases Hx' with ⟨x, Hx, rfl⟩
      apply H.open_map x U
      simp [neighborOf, NeighborOf]
      use U, HU, Hx, by simp
  · refine {
      continuous := by
        have H' := congr_arg (@Topology.isOpen X) H
        rw [IsContinuous_iff]
        intro U HU
        rw [H'] at ⊢
        apply GenedOpen.base
        simp [Init.subbase, Init.to]
        use U, HU
      bij := Hf
      open_map := by
        intro x U Hx
        simp [neighborOf, NeighborOf] at Hx ⊢
        rcases Hx with ⟨V, HV, Vx, VU⟩
        use f '' V; constructor; swap
        · constructor<;> grind
        · clear VU Vx
          rw [H] at HV; clear H
          induction HV with
          | base W HW =>
            simp [Init.subbase, Init.to] at HW
            rcases HW with ⟨W', HW', rfl⟩
            rw [Set.image_preimage_eq _ Hf.2]
            exact HW'
          | univ =>
            simp; rw [Hf.2.range_eq]
            apply HX'.isOpen_univ
          | inter S T HS HT IHS IHT =>
            rw [Set.image_inter Hf.1]
            apply HX'.isOpen_inter _ _ IHS IHT
          | union S HS IH =>
            rw [Set.image_sUnion]
            apply HX'.isOpen_sUnion
            intro s Hs; simp at Hs
            rcases Hs with ⟨W, HW, rfl⟩
            apply IH _ HW
    }

end ex_2_3
