import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod
import Bourbaki.Topology.ch1_topology.ss4_1_prod'
import Bourbaki.Topology.ch1_topology.ss4_2_section

namespace Bourbaki



lemma mem_closure_iff_neighborWithin [HX : Topology X] (x : X) (s : Set X) :
  x ∈ closure s ↔ ∅ ∉ neighborWithin x s
:= by
  rw [mem_closure_iff]; simp [neighborWithin, neighborOf, NeighborOf]
  constructor<;> intro H
  · intro U HU Ux F
    apply H U U HU Ux (by simp)
    rw [Set.inter_comm, F]
  · intro B U HU Ux UB F
    apply H U HU Ux
    ext y; simp
    intro Uy sy
    apply UB at Uy
    have : y ∈ s ∩ B := by {grind}; grind



-- TODO: 逆の証明には近傍フィルターが必要そう？
lemma prod.closure_eq {I : Type _} {X : I → Type _}  [HX : ∀ i, Topology (X i)] (A : ∀ i, Set (X i)) :
  closure (subprod A) ⊆ subprod (fun i => closure (A i))
:= by
  intro f
  simp [subprod, Set.pi]
  intro H i
  rw [mem_closure_iff] at ⊢ H
  intro B HB F
  have Hi := prod.isContinuous X i f B HB
  apply H at Hi
  apply Hi
  ext g; simp
  intro HA HB
  have : g i ∈ A i ∩ B := by {grind}; grind
