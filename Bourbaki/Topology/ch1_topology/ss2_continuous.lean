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

lemma IsContinuousAt_compose [Topology X] [Topology X'] [Topology X''] {f : X → X'} {g : X' → X''}
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
    · rw [mem_closure_iff_adherent]
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
    rw [mem_closure_iff_adherent]
    intro U HU F
    have : f x ∈ f '' A ∩ U := by {
      simp; constructor; use x
      apply neighborOf_mem_self HU
    }
    grind

lemma IsContinuous_iff_IsOpen_preimage [HX : Topology X] [HX' : Topology X'] (f : X → X') :
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
