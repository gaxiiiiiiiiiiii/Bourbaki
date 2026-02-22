import Bourbaki.Set.ch3_Order.ss7_1_inverseLimit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

namespace Bourbaki

open CategoryTheory
open Opposite
open Limits



#check HasLimitsOfShape

def InvSystem.Sub [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) := MonoOver E

def InvSystem.Sub.invSystem [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) :
  InvSystem I 𝓒
:= S.obj.left

noncomputable def InvSystem.Sub.limMap [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit (S.invSystem)] :
  S.invSystem.limit ⟶ E.limit
:= Limits.limMap S.obj.hom

lemma InvSystem.Sub.limMap_mono [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit (S.invSystem)] :
  Mono (S.limMap)
:= by
  constructor; intro c f g H
  apply InvSystem.hom_ext
  intro i
  let C : InvSystem I 𝓒 := (CategoryTheory.Functor.const (J := Iᵒᵖ)).obj c
  let F : C ⟶ S.invSystem := {
    app i := f ≫ S.invSystem.π i.unop
    naturality := by intro i j h; simp [C, InvSystem.π]
  }
  let G : C ⟶ S.invSystem := {
    app i := g ≫ S.invSystem.π i.unop
    naturality := by intro i j h; simp [C, InvSystem.π]
  }
  suffices : F = G
  rw [CategoryTheory.NatTrans.ext_iff] at this
  have := congr_fun this (op i)
  simp [F, G] at this; assumption
  apply S.property.right_cancellation
  apply NatTrans.ext; ext j; simp [F, G]
  simp [InvSystem.π]
  rw [<- Limits.limMap_π, <- Category.assoc]
  simp [InvSystem.Sub.limMap] at H
  grind



-- 流石に重すぎるからコメントアウト
-- MathlibのPreservesPullback.isoを使うと早いからそっちを使う
-- set_option maxHeartbeats 1000000
-- CategoryTheory.Limits.PreservesPullback.iso
-- noncomputable def InvSystem.Sub.PreservesPullback [Preorder I] [Category 𝓒] {E E' : InvSystem I 𝓒}
--   (u : E ⟶ E') (S' : E'.Sub) [HasLimitsOfShape Iᵒᵖ 𝓒] [HasPullbacks 𝓒]:
--   (pullback u S'.arrow).limit ≅ pullback (InvSystem.limMap u) (InvSystem.limMap S'.arrow)
-- := by
--   let hom : (pullback u (MonoOver.arrow S')).limit ⟶ pullback (InvSystem.limMap u) (InvSystem.limMap (MonoOver.arrow S')) := by
--     apply pullback.lift ?_ ?_ ?_
--     · apply InvSystem.limMap (pullback.fst u (MonoOver.arrow S'))
--     · apply InvSystem.limMap (pullback.snd u (MonoOver.arrow S'))
--     · simp [InvSystem.limMap]
--       apply limit.hom_ext; intro i; simp
--       rw [<- NatTrans.comp_app, <- NatTrans.comp_app]
--       rw [pullback.condition]
--   let c : Cone (pullback u (MonoOver.arrow S')) := {
--     pt := pullback (InvSystem.limMap u) (InvSystem.limMap (MonoOver.arrow S'))
--     π := by
--       apply pullback.lift ?_ ?_ ?_
--       · refine {
--           app i := pullback.fst (InvSystem.limMap u) (InvSystem.limMap (MonoOver.arrow S')) ≫ E.π i.unop
--           naturality {i j} f := by simp [InvSystem.π]
--         }
--       · refine {
--           app i := pullback.snd (InvSystem.limMap u) (InvSystem.limMap (MonoOver.arrow S')) ≫ S'.invSystem.π i.unop
--           naturality {i j} f := by simp [InvSystem.π, invSystem]
--         }
--       · apply NatTrans.ext; simp
--         ext i; simp
--         rw [<-  InvSystem.limMap_π, <-  InvSystem.limMap_π]
--         rw [<- Category.assoc, pullback.condition]; grind
--   }

--   refine {
--   hom := hom
--   inv := limit.lift (pullback u (MonoOver.arrow S')) c
--   hom_inv_id := by
--     apply limit.hom_ext; intro i; simp
--     let C : InvSystem I 𝓒 := (CategoryTheory.Functor.const (J := Iᵒᵖ)).obj (pullback u (MonoOver.arrow S')).limit
--     let L : C ⟶ (pullback u (MonoOver.arrow S')) := {
--       app i := hom ≫ c.π.app i
--       naturality := by intro i j h; simp [C]
--     }
--     let R : C ⟶ (pullback u (MonoOver.arrow S')) := {
--       app i := limit.π (pullback u (MonoOver.arrow S')) i
--       naturality := by intro i j h; simp [C]
--     }
--     suffices : L = R
--     rw [CategoryTheory.NatTrans.ext_iff] at this
--     have := congr_fun this i
--     simp [L, R] at this; assumption
--     apply pullback.hom_ext<;> simp [L, R]<;>
--     apply NatTrans.ext<;> ext i<;>
--     simp [c, hom, InvSystem.limMap, InvSystem.π, invSystem]
--   inv_hom_id := by
--     simp [hom, c]
--     apply pullback.hom_ext<;>
--     apply limit.hom_ext<;> intro i<;>
--     simp [InvSystem.limMap, InvSystem.π]; rfl
-- }

-- TODO
-- example [Preorder I] [Category 𝓒]  [HasLimitsOfShape Iᵒᵖ 𝓒] {E E' : InvSystem I 𝓒} (u : E ⟶ E') (S' : E'.Sub) :
  -- PreservesLimit (cospan u S'.arrow) Limits.lim


-- TODO
-- CategoryTheory.Limits.PreservesPullback.iso
noncomputable def InvSystem.Sub.PreservesPullback [Preorder I] [Category 𝓒] {E E' : InvSystem I 𝓒}
  (u : E ⟶ E') (S' : E'.Sub) [HasLimitsOfShape Iᵒᵖ 𝓒] [HasPullbacks 𝓒]:
  (pullback u S'.arrow).limit ≅ pullback (InvSystem.limMap u) (InvSystem.limMap S'.arrow)
:= by
  change Limits.lim.obj (pullback u S'.arrow) ≅ pullback (Limits.lim.map u) (Limits.lim.map S'.arrow)
  apply CategoryTheory.Limits.PreservesPullback.iso












end Bourbaki
