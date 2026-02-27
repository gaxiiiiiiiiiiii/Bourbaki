import Bourbaki.Set.ch3_Order.ss7_1_inverseLimit
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

namespace Bourbaki

open CategoryTheory
open Opposite
open Limits



#check HasLimitsOfShape

def InvSystem.Sub [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) := MonoOver E

def InvSystem.Sub.invSystem [SmallCategory I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) :
  InvSystem I 𝓒
:= S.obj.left

noncomputable def InvSystem.Sub.limMap [SmallCategory I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit (S.invSystem)] :
  limit (S.invSystem) ⟶ limit E
:= Limits.limMap S.obj.hom

lemma InvSystem.limMap_mono [SmallCategory I] [Category 𝓒] {E E' : InvSystem I 𝓒}  [HasLimit E] [HasLimit E']  (u : E ⟶ E') (Hu : Mono u):
  Mono (Limits.limMap u)
:= by
  constructor; intro c f g H
  apply limit.hom_ext; intro i
  let C : InvSystem I 𝓒 := (CategoryTheory.Functor.const (J := Iᵒᵖ)).obj c
  let F : C ⟶ E := {
    app i := f ≫ limit.π E i
    naturality := by intro i j h; simp [C]
  }
  let G : C ⟶ E := {
    app i := g ≫ limit.π E i
    naturality := by intro i j h; simp [C]
  }
  have : F = G := by {
    apply Hu.right_cancellation
    apply NatTrans.ext; ext i; simp [F, G]
    -- simp [InvSystem.π]
    rw [<- Limits.limMap_π, <- Category.assoc, H, Category.assoc]
  }
  rw [CategoryTheory.NatTrans.ext_iff] at this
  have := congr_fun this i
  simp [F, G] at this; assumption

lemma InvSystem.Sub.limMap_mono [SmallCategory I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit (S.invSystem)] :
  Mono (S.limMap)
:= by
  simp [InvSystem.Sub.limMap]
  apply InvSystem.limMap_mono
  apply S.property




-- 流石に重すぎるからコメントアウト
-- MathlibのPreservesPullback.isoを使うと早いからそっちを使う
-- set_option maxHeartbeats 1000000
-- noncomputable def InvSystem.Sub.PreservesPullback [SmallCategory I] [Category 𝓒] {E E' : InvSystem I 𝓒}
--   (u : E ⟶ E') (S' : E'.Sub) [HasLimitsOfShape Iᵒᵖ 𝓒] [HasPullbacks 𝓒]:
--   (pullback u S'.arrow).limit ≅ pullback (Limits.lim.map u) (Limits.lim.map S'.arrow)
-- := by
--   let hom : (pullback u (MonoOver.arrow S')).limit ⟶ pullback (Limits.lim.map u) (Limits.lim.map (MonoOver.arrow S')) := by
--     apply pullback.lift ?_ ?_ ?_
--     · apply Limits.lim.map (pullback.fst u (MonoOver.arrow S'))
--     · apply Limits.lim.map (pullback.snd u (MonoOver.arrow S'))
--     · simp --[InvSystem.limMap]
--       apply limit.hom_ext; intro i; simp
--       rw [<- NatTrans.comp_app, <- NatTrans.comp_app]
--       rw [pullback.condition]
--   let c : Cone (pullback u (MonoOver.arrow S')) := {
--     pt := pullback (Limits.lim.map u) (Limits.lim.map (MonoOver.arrow S'))
--     π := by
--       apply pullback.lift ?_ ?_ ?_
--       · refine {
--           app i := pullback.fst (Limits.lim.map u) (Limits.lim.map (MonoOver.arrow S')) ≫ limit.π E i
--           naturality {i j} f := by simp --[InvSystem.π]
--         }
--       · refine {
--           app i := pullback.snd (Limits.lim.map u) (Limits.lim.map (MonoOver.arrow S')) ≫ limit.π S'.invSystem i
--           naturality {i j} f := by simp [invSystem]
--         }
--       · apply NatTrans.ext; simp
--         ext i; simp
--         rw [<-  Limits.limMap_π, <-  Limits.limMap_π]
--         rw [<- Category.assoc, pullback.condition]; grind
--   }

--   refine {
--     hom := hom
--     inv := limit.lift (pullback u (MonoOver.arrow S')) c
--     hom_inv_id := by
--       apply limit.hom_ext; intro i; simp
--       let C : InvSystem I 𝓒 := (CategoryTheory.Functor.const (J := Iᵒᵖ)).obj (pullback u (MonoOver.arrow S')).limit
--       let L : C ⟶ (pullback u (MonoOver.arrow S')) := {
--         app i := hom ≫ c.π.app i
--         naturality := by intro i j h; simp [C]
--       }
--       let R : C ⟶ (pullback u (MonoOver.arrow S')) := {
--         app i := limit.π (pullback u (MonoOver.arrow S')) i
--         naturality := by intro i j h; simp [C]
--       }
--       suffices : L = R
--       rw [CategoryTheory.NatTrans.ext_iff] at this
--       have := congr_fun this i
--       simp [L, R] at this; assumption
--       apply pullback.hom_ext<;> simp [L, R]<;>
--       apply NatTrans.ext<;> ext i<;>
--       simp [c, hom, invSystem]
--     inv_hom_id := by
--       simp [hom, c]
--       apply pullback.hom_ext<;>
--       apply limit.hom_ext<;> intro i<;> simp; rfl
-- }

-- TODO
example [SmallCategory I] [Category 𝓒]  [HasLimitsOfShape Iᵒᵖ 𝓒] {E E' : InvSystem I 𝓒} (u : E ⟶ E') (S' : E'.Sub) :
  PreservesLimit (cospan u S'.arrow) Limits.lim
:= by
  simpa [InvSystem.Sub] using (inferInstance : PreservesLimit (cospan u (MonoOver.arrow S')) Limits.lim)



-- TODO
-- CategoryTheory.Limits.PreservesPullback.iso
noncomputable def InvSystem.Sub.PreservesPullback [SmallCategory I] [Category 𝓒] {E E' : InvSystem I 𝓒}
  (u : E ⟶ E') (S' : E'.Sub) [HasLimitsOfShape Iᵒᵖ 𝓒] [HasPullbacks 𝓒]:
  limit (pullback u S'.arrow) ≅ pullback (Limits.lim.map u) (Limits.lim.map S'.arrow)
:= by
  change Limits.lim.obj (pullback u S'.arrow) ≅ pullback (Limits.lim.map u) (Limits.lim.map S'.arrow)
  apply CategoryTheory.Limits.PreservesPullback.iso



-- TODO  Functor.Initial.induction
#check Functor.Initial.extendCone
noncomputable example [Category 𝓒] [Category 𝓓] [Category 𝓔] (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) [F.Initial] [HasLimit G] :
  Cone (F ⋙ G) ⥤ Cone G
where
  obj c := {
    pt := c.pt
    π := {
      app d := c.π.app (Functor.Initial.lift F d) ≫ G.map (Functor.Initial.homToLift F d)
      naturality {d d'} f := by
        simp
        apply Functor.Initial.induction F fun Z k => (c.π.app Z ≫ G.map k : c.pt ⟶ _) = c.π.app (Functor.Initial.lift F d) ≫ G.map (Functor.Initial.homToLift F d) ≫ G.map f
        · intro x y X Y u E H
          rw [<- H, <- E]; simp
          rw [<- Category.assoc, <- Functor.comp_map]
          rw [<-  c.π.naturality u]; simp
        · intro x y X Y u E H
          rw [<- H, <- E]
          simp
          rw [<- Category.assoc, <- Functor.comp_map]
          rw [<- c.π.naturality]; simp
        · rw [<- Functor.map_comp]
    }
  }
  map {C C'} f := {hom := f.hom}


-- 自前で実装はできたけど、Functor.Initialを使った方がエレガントで早そうだから、そっちを使う
noncomputable def InvSystem.restrict_limit_equiv [SmallCategory I] [Category 𝓒]
  (J : SubIndex I) [J.functor.op.Initial]
   (E : InvSystem I 𝓒)[HasLimit E] [HasLimit (E.restrict J)] [HasLimit (J.functor.op ⋙ E)]
  :
   limit E ≅ limit (E.restrict J)
where
  hom := restrict.limMap E J
  inv := limit.lift E (Functor.Initial.extendCone.obj (limit.cone (E.restrict J)))
  hom_inv_id := by
    apply limit.hom_ext; intro i; simp [restrict.limMap]
  inv_hom_id := by
    apply limit.hom_ext; intro i
    simp [restrict.limMap]
    apply Functor.Initial.induction J.functor.op fun Z k => limit.π (J.functor.op ⋙ E) Z ≫ E.map k = limit.π (E.restrict J) i
    · intro x y X Y u HX H
      rw [<- H, <- HX]
      rw [<- limit.w (J.functor.op ⋙ E) u]
      simp

    · intro x y X Y u HX H
      rw [<- H, <- HX]; simp
      rw [<- limit.w (J.functor.op ⋙ E) u]
      simp
    · exact  limit.w (J.functor.op ⋙ E) (𝟙 i)


-- TODO
#check Functor.Initial.limitIso
noncomputable def InvSystem.restrict.limitIso [SmallCategory I] [Category 𝓒]
  (E : InvSystem I 𝓒)[HasLimit E]
  (J : SubIndex I) [HJ : J.functor.op.Initial] [HasLimit (E.restrict J)] :
  limit (E.restrict J) ≅ limit E
:= Functor.Initial.limitIso J.functor.op E



-- noncomputable def InvSystem.limImage [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) [HasLimit E] [HasImages 𝓒] [HasImageMaps 𝓒] : --[∀ i, HasImage (E.π i)]:
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


noncomputable def InvSystem.limImage [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) [HasLimit E] [HasImages (Iᵒᵖ ⥤ 𝓒)] [HasImageMaps (Iᵒᵖ ⥤ 𝓒)] :
  E.Sub
:= MonoOver.mk (image.ι (limit.cone E).π)


noncomputable def InvSystem.limImage_limit_iso [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) [HasLimit E] [HasImages (Iᵒᵖ ⥤ 𝓒)] [HasImageMaps (Iᵒᵖ ⥤ 𝓒)] [HasLimit E.limImage.invSystem] [HasLimit (image (limit.cone E).π)] :
  limit E.limImage.invSystem ≅ limit E
:= by
  let c : Cone (image (limit.cone E).π) := {
    pt := limit E
    π := (factorThruImage ((limit.cone E).π))
  }
  refine {
    hom := Limits.limMap (image.ι (limit.cone E).π)
    inv := limit.lift (image (limit.cone E).π : InvSystem I 𝓒) c
    hom_inv_id := by
      apply limit.hom_ext; intro i; simp
      let C : InvSystem I 𝓒 := (Functor.const (J := Iᵒᵖ)).obj (Limits.limit (image (limit.cone E).π))
      let L : C ⟶ (image (limit.cone E).π) := {
        app i := limMap (image.ι (limit.cone E).π) ≫ limit.lift (image (limit.cone E).π) c ≫ limit.π E.limImage.invSystem i
        naturality i j f := by simp [C]; rw [<- limit.w (E.limImage.invSystem) f]; rfl
      }
      let R : C ⟶ (image (limit.cone E).π) := {
        app i := limit.π E.limImage.invSystem i
        naturality i j f := by simp [C]; rw [<-  limit.w E.limImage.invSystem f]; rfl
      }
      suffices : L = R
      rw [CategoryTheory.NatTrans.ext_iff] at this
      have := congr_fun this i
      simp [L, R] at this; assumption

      have : Mono (image.ι (limit.cone E).π) := by infer_instance
      apply this.right_cancellation

      apply NatTrans.ext
      ext i; simp [L, R]
      simp [Sub.invSystem, limImage, c]
      rw [<- limMap_π ( α := (image.ι (limit.cone E).π))]
      rw [<- NatTrans.comp_app, image.fac]
      rfl
    inv_hom_id := by
      apply limit.hom_ext; intro i; simp [c]
  }









end Bourbaki
