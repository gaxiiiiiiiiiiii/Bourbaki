import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3

namespace Bourbaki

section ex_3_1

variable [Topology X] (A B : Set X) (BA : B ⊆ A)

example :
   {x : A | x.val ∈ interior B} ⊆ interior (HX := Subtopology A) {x : A | x.val ∈ B}
:= by
  intro x Hx; simp at Hx ⊢
  rw [mem_interior_iff] at Hx ⊢
  rcases Hx with ⟨U, HU, E⟩
  use {x : A | x.val ∈ U}
  rw [Subtopology.neighborOf_iff]
  constructor
  · use U, HU, by simp
  · ext x; simp
    intro Ux
    by_contra (Bx : x.val ∈ Bᶜ)
    have : x.val ∈ U ∩ Bᶜ := by grind
    rw [E] at this; contradiction

example :
  frontier (HX := Subtopology A) {x | x.val ∈ B} ⊆ {x : A | x.val ∈ frontier B}
:= by
  intro x Hx; simp
  rw [mem_frontier_iff] at Hx ⊢
  intro U HU
  have : {x : A | x.val ∈ U} ∈ neighborOf x := by {
    rw [Subtopology.neighborOf_iff]
    use U, HU, by simp
  }
  apply Hx at this
  rcases this with ⟨H1, H2⟩
  constructor<;> intro F
  · apply H1; ext x; simp
    intro Bx Ux
    have : x.val ∈ U ∩ B := by grind
    grind
  · apply H2; ext x; simp
    intro Bc Ux
    have : x.val ∈ U ∩ Bᶜ := by grind
    grind

end ex_3_1

section ex_3_2

variable [Topology X] (A B : Set X)

example :
  -- {x : A | x.val ∈ interior B} ⊆ interior (HX := Subtopology A) {x : A | x.val ∈ B}
  closure (HX := Subtopology A) {x | x.val ∈ B} ⊆ {x : A | x.val ∈ closure B}
:= by
  intro x Hx; simp
  rw [mem_closure_iff] at Hx ⊢
  intro U HU F
  have : {x : A | x.val ∈ U} ∈ neighborOf x := by {
    rw [Subtopology.neighborOf_iff]; use U
  }
  apply Hx at this
  apply this; ext x; simp
  intro Bx Ux
  have : x.val ∈ B ∩ U := by grind
  grind

end ex_3_2


