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

noncomputable def InvSystem.restrict.limMap [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) (J : MonoOver I) [HasLimit E] [HasLimit (E.restrict J)] :
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

noncomputable def InvSystem.restrict.lmMap
   [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} {J K : MonoOver I}
  [HasLimit E] [HasLimit (E.restrict J)] [HasLimit (E.restrict K)]
  (u : J ⟶ K) :
  (E.restrict K).limit ⟶ (E.restrict J).limit
:= by

  let jk (j : J.obj.leftᵒᵖ) : J.arrow (unop j) ⟶ K.arrow (u.hom.left (unop j)) := by {
    have Hw := u.hom.w
    conv at Hw => arg 1; arg 1; simp
    conv at Hw => arg 2; simp
    simp [MonoOver.arrow]
    rw [<- Hw]; simp
    exact 𝟙 _
  }

  let c : Cone (E.restrict J) := {
    pt := (E.restrict K).limit
    π := {
      app j := (E.restrict K).π (u.hom.left j.unop) ≫ E.map (jk j).op
      naturality {j j'} f := by
        simp
        let f' := J.functor.map f.unop
        simp [MonoOver.functor, MonoOver.arrow ] at f'
        have Hw := u.hom.w
        conv at Hw => arg 1; arg 1; simp
        conv at Hw => arg 2; simp
        rw [<- Hw] at f'; simp at f'
        have Jw := limit.w (E.restrict K) f'.op
        conv at Jw => arg 2; change limit.π (E.restrict K) (op (u.hom.left (unop j')))
        simp [InvSystem.π]
        rw [<- Jw]
        set g := (limit.π (E.restrict K) (op (u.hom.1 (unop j))))
        simp [InvSystem.restrict]
        rw [<- CategoryTheory.Functor.map_comp, <- CategoryTheory.Functor.map_comp]
        suffices :((K.functor.map f'.op.unop).op ≫ (jk j').op  ) =((jk j).op ≫ (J.functor.map f.unop).op)
        rw [<- this]; rfl
        apply Subsingleton.elim
    }
  }
  exact  (E.restrict J).lift c



end Bourbaki
