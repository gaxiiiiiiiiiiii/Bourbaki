import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod
import Bourbaki.Topology.ch1_topology.ss4_1_prod'
import Bourbaki.Topology.ch1_topology.ss4_2_section
import Bourbaki.Topology.ch1_topology.ss4_3_closure
import Bourbaki.Set.ch3_Order.ss7_1_inverseLimit
import Bourbaki.Set.ch3_Order.ss7_2_map





namespace Bourbaki
open CategoryTheory
open Opposite
open Limits


structure TOP where
  carrier : Type _
  isTopology : Topology carrier


instance : CoeSort TOP (Type _) := ⟨TOP.carrier⟩

instance (X : TOP) : Topology X := X.isTopology


structure TOP.Hom (X Y : TOP) where
  toFun : X.carrier → Y.carrier
  isContinuous : IsContinuous toFun


instance Topology.category :
  Category TOP
where
  Hom X Y := TOP.Hom X Y
  id X := {
    toFun := id
    isContinuous := by
      intro x S; simp
  }
  comp {X Y Z} f g := {
    toFun := g.toFun ∘ f.toFun
    isContinuous := IsContinuous_comp f.isContinuous g.isContinuous
  }


instance (X Y : TOP) : CoeFun (X ⟶ Y) (fun _ => X.carrier → Y.carrier) := ⟨TOP.Hom.toFun⟩




def InvSystem.topology [SmallCategory I] (E : InvSystem I TOP) [HasLimit E] :
  Topology (↑(limit E))
:= Init.topology  (fun (i : Iᵒᵖ) (x : (limit E).carrier) => limit.π E i x)


def InvSystem.Sub.limSet [SmallCategory I] {E : InvSystem I TOP} [HasLimit E]
  (F : E.Sub) [HasLimit F.obj.left] :
  Set (limit E).carrier
:= Set.range (Limits.limMap F.arrow)

def InvSystem.Sub.topology
  [SmallCategory I] {E : InvSystem I TOP} [HasLimit E]
  (F : E.Sub) [HasLimit F.obj.left]
  : Topology ↑F.limSet
:= Subtopology (F.limSet)



noncomputable example
  [SmallCategory I] (X  : InvSystem I TOP) [HasLimit X]
  (J : SubIndex I) [HJ : J.functor.op.Initial] [HasLimit (X.restrict J)] :
  limit (X.restrict J) ≅ limit X
:= InvSystem.restrict.limitIso X J
