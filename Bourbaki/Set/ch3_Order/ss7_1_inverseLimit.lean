import Bourbaki.Set.ch3_Order.invSystem

open CategoryTheory
open Opposite
open Limits

namespace Bourbaki

instance [Preorder I] (J : MonoOver I) :
  Preorder J.obj.left
:= Preorder.lift J.arrow

instance [Preorder I] (J : MonoOver I) :
  Category (J.obj.left)
:= Preorder.smallCategory J.obj.left

def _root_.CategoryTheory.MonoOver.functor [Preorder I] (J : MonoOver I) :
  J.obj.left ⥤ I
:= {
  obj i := J.arrow i
  map  f :=  ⟨⟨f.down.down⟩⟩
  map_id _ :=  Eq.symm (eq_of_comp_right_eq fun {_} ↦ congrFun rfl)
  map_comp _ _ := Eq.symm (eq_of_comp_right_eq fun {_} ↦ congrFun rfl)
}


def InvSystem.restrict [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) (J : MonoOver I) :
  InvSystem J.obj.left 𝓒
:= J.functor.op ⋙ E

noncomputable def InvSystem.restrict.limMap [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (J : MonoOver I) [HasLimit E] [HasLimit (E.restrict J)] :
  E.limit ⟶ (E.restrict J).limit
:= by
  let c : Cone (E.restrict J) := {
    pt := E.limit
    π := {
      app i := by
        simp [InvSystem.restrict, MonoOver.functor]
        exact E.π (J.arrow i.unop)
      naturality {i j} f := by
        simp [InvSystem.restrict, MonoOver.functor, InvSystem.π]
    }
  }
  exact (E.restrict J).lift c


end Bourbaki
