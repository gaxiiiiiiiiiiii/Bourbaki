import Bourbaki.Set.ch3_Order.invSystem

open CategoryTheory
open Opposite
open Limits

namespace Bourbaki

def InvSystem.sub [Preorder I] [Category 𝓒] (S : InvSystem I 𝓒) (J : Set I):
  InvSystem J 𝓒
where
  obj i := S.obj (op i.unop.val)
  map {i j } f := by
    apply S.map
    exact WithTerminal.down f
  map_id := by
    intro i
    simp [WithTerminal.down]
    exact S.map_id (op ↑(unop i))
  map_comp := by
    intro i j k f g
    simp [WithTerminal.down]
    apply S.map_comp

noncomputable def InvSystem.subMap [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} (J : Set I) [HasLimit S] [HasLimit (S.sub J)] :
  S.limit ⟶ (S.sub J).limit
:= by
  let c : Cone (S.sub J) := {
    pt := S.limit
    π := {
      app i := by
        simp [InvSystem.sub]
        exact  S.π i.unop.val
      naturality := by
        intro i j f
        simp [InvSystem.sub, WithTerminal.down]
        have H : j.unop.val ≤ i.unop.val := by
          simp; exact f.unop.down.down
        rw [<- S.w H]; rfl
    }
  }
  apply (S.sub J).lift c

end Bourbaki
