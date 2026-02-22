import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod
import Bourbaki.Topology.ch1_topology.ss4_1_prod'
import Bourbaki.Topology.ch1_topology.ss4_2_section
import Bourbaki.Topology.ch1_topology.ss4_3_closure





namespace Bourbaki

structure InvSystem [Preorder I] (X : I → Type k)  where
  map {i j} : i ≤ j →  X j → X i
  map_id : ∀ i, map (le_refl i) = id
  map_comp : ∀ {i j k} (Hij : i ≤ j) (Hjk : j ≤ k),
     map Hij ∘ map Hjk = map (le_trans Hij Hjk)

def InvSystem.limit [Preorder I] {X : I → Type _}  (S : InvSystem X) :=
  {f : Π i, X i | ∀ i j (H : i ≤ j), f i = S.map H (f j)}

def InvSystem.proj  [Preorder I] {X : I → Type _} (S : InvSystem X) (i : I) :
  limit S → X i
:= fun f => f.val i


structure InvSystem.isContinuous [Preorder I] {X : I → Type _} [∀ i, Topology (X i)] (S : InvSystem X) : Prop where
  continuous : ∀ {i j} (Hij : i ≤ j), IsContinuous (S.map Hij)

def InvSystem.topology {I : Type _} [Preorder I] {X : I → Type _} [∀ i, Topology (X i)] (S : InvSystem X) :
  Topology (limit S)
:= Init.topology (proj S)


--TODO 部分の逆系について
