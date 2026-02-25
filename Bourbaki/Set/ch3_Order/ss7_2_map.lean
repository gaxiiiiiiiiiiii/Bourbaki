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

lemma InvSystem.limMap_mono [Preorder I] [Category 𝓒] {E E' : InvSystem I 𝓒}  [HasLimit E] [HasLimit E']  (u : E ⟶ E') (Hu : Mono u):
  Mono (Limits.limMap u)
:= by
  constructor; intro c f g H
  apply limit.hom_ext; intro i
  let C : InvSystem I 𝓒 := (CategoryTheory.Functor.const (J := Iᵒᵖ)).obj c
  let F : C ⟶ E := {
    app i := f ≫ E.π i.unop
    naturality := by intro i j h; simp [C, InvSystem.π]
  }
  let G : C ⟶ E := {
    app i := g ≫ E.π i.unop
    naturality := by intro i j h; simp [C, InvSystem.π]
  }
  have : F = G := by{
    apply Hu.right_cancellation
    apply NatTrans.ext; ext i; simp [F, G]
    simp [InvSystem.π]
    rw [<- Limits.limMap_π, <- Category.assoc, H, Category.assoc]
  }
  rw [CategoryTheory.NatTrans.ext_iff] at this
  have := congr_fun this i
  simp [F, G] at this; assumption

lemma InvSystem.Sub.limMap_mono [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit (S.invSystem)] :
  Mono (S.limMap)
:= by
  simp [InvSystem.Sub.limMap]
  apply InvSystem.limMap_mono
  apply S.property




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


-- 自前で実装はできたけど、Functor.Initialを使った方がエレガントで早そうだから、そっちを使う
-- noncomputable def InvSystem.restrict_limit_equiv [Preorder I] [Category 𝓒]
--   (J : MonoOver I) (HJ1 : IsDirectedOrder J.obj.left)
--   (HJ2 : ∀ i : I, ∃ j : J.obj.left, i ≤ J.arrow j )
--    (E : InvSystem I 𝓒)[HasLimit E] [HasLimit (E.restrict J)] [HasLimit (J.functor.op ⋙ E)]
--   :
--    E.limit ≅ (E.restrict J).limit
-- := by
--   let c : Cone E := {
--     pt := (E.restrict J).limit
--     π := {
--       app i := (E.restrict J).π ((HJ2 i.unop).choose) ≫ E.mapOf (HJ2 i.unop).choose_spec
--       naturality {i j} f := by
--         simp
--         have Hi := (HJ2 (unop i)).choose_spec
--         have Hj := (HJ2 (unop j)).choose_spec
--         set i' := (HJ2 (unop i)).choose
--         set j' := (HJ2 (unop j)).choose
--         have ⟨c, ic, jc⟩ := HJ1.directed i' j'
--         have Ei := (E.restrict J).w ic
--         have Ej := (E.restrict J).w jc
--         conv => arg 1; arg 1; change (E.restrict J).π j'
--         conv => arg 2; arg 1; change (E.restrict J).π i'
--         rw [<- Ei, <- Ej]; simp
--         simp [mapOf, InvSystem.restrict]
--         rw [<- CategoryTheory.Functor.map_comp, <- CategoryTheory.Functor.map_comp, <- CategoryTheory.Functor.map_comp]
--         suffices : ((J.functor.map (homOfLE jc)).op ≫ (homOfLE Hj).op) = ((J.functor.map (homOfLE ic)).op ≫ (homOfLE Hi).op ≫ f)
--         rw [this]
--         apply Subsingleton.elim
--     }
--   }
--   refine {
--     hom := restrict.limMap E J
--     inv := E.lift c
--     hom_inv_id := by
--       apply E.hom_ext; intro i; simp
--       rw [E.lift_π c]
--       simp [restrict.limMap, c]
--       rw [<- Category.assoc, (E.restrict J).lift_π]; simp
--       rw [E.w]
--     inv_hom_id := by
--       apply (E.restrict J).hom_ext; intro i; simp
--       simp [restrict.limMap]
--       rw [((E.restrict J)).lift_π]; simp
--       rw [E.lift_π]
--       simp [c]
--       have ⟨j, Hj⟩ := HJ2 (J.arrow i)
--       have Hj :=( HJ2 (J.arrow i)).choose_spec
--       set j := (HJ2 (J.arrow i)).choose
--       change (E.restrict J).π j ≫ mapOf Hj = (E.restrict J).π i
--       rw [(E.restrict J).w Hj]
--   }

-- TODO
-- Functor.Initial.limitIso
noncomputable def InvSystem.restrict.limitIso [Preorder I] [Category 𝓒]
  (E : InvSystem I 𝓒)[HasLimit E]
  (J : MonoOver I) [HJ : J.functor.op.Initial] [HasLimit (E.restrict J)] :
  (E.restrict J).limit ≅ E.limit
:= Functor.Initial.limitIso J.functor.op E



-- noncomputable def InvSystem.limImage [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) [HasLimit E] [HasImages 𝓒] [HasImageMaps 𝓒] : --[∀ i, HasImage (E.π i)]:
--   E.Sub
-- := by
--   let hom {i j : Iᵒᵖ} (f : i ⟶ j) : Arrow.mk (E.π i.unop) ⟶ Arrow.mk (E.π j.unop) := by
--     apply Arrow.homMk' (𝟙 E.limit) (E.map f) ?_
--     simp [InvSystem.π]

--   refine {
--     obj := {
--       left := {
--         obj i := image (E.π i.unop)
--         map {i j} f := (HasImageMap.imageMap (hom f)).map
--       }
--       right := ⟨PUnit.unit⟩
--       hom := {
--         app i := Limits.image.ι ((E.π (unop i)))
--         naturality {i j} f := by
--           simp
--           have  := (HasImageMap.imageMap (hom f)).map_ι ; simp at this
--           rw [this]
--           simp [hom]
--       }
--     }
--     property := by
--       constructor
--       intro E' g h H; simp at *
--       apply NatTrans.ext; ext i; simp
--       rw [NatTrans.ext_iff] at H
--       have := congr_fun H i; simp at this
--       apply Mono.right_cancellation
--   }


noncomputable def InvSystem.limImage [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) [HasLimit E] [HasImages (Iᵒᵖ ⥤ 𝓒)] [HasImageMaps (Iᵒᵖ ⥤ 𝓒)] : --[∀ i, HasImage (E.π i)]:
  E.Sub
:= MonoOver.mk (image.ι (limit.cone E).π)





end Bourbaki
