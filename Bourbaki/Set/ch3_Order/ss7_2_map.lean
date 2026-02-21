import Bourbaki.Set.ch3_Order.ss7_1_inverseLimit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

namespace Bourbaki

open CategoryTheory
open Opposite
open Limits


lemma InvSystem.limMap_π
  [Preorder I] [Category 𝓒] {E F : InvSystem I 𝓒}
  [HasLimit E] [HasLimit F]
  (u : E ⟶ F) (i : I) :
  limMap u ≫ F.π i = E.π i ≫ u.app (op i)
:= by simp [limMap, InvSystem.π]


lemma InvSystem.map_comp
  [Preorder I] [Category 𝓒] {E F G : InvSystem I 𝓒}
  [HasLimit E] [HasLimit F] [HasLimit G]
  (u : E ⟶ F) (v : F ⟶ G) :
  limMap (u ≫ v) = limMap u ≫ limMap v
:= by
  apply limMap_ext
  intro i
  rw [Category.assoc, limMap_π, limMap_π, <- Category.assoc, limMap_π]
  simp



structure InvSystem.Sub [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) : Type where
  hom i : Subobject (E.proj (op i))
  map {i j : I} (H : i ≤ j)  : Subobject.underlying.obj (hom j) ⟶ Subobject.underlying.obj (hom i)
  fac { i j : I} (H : i ≤ j) : map H ≫ (hom i).arrow = (hom j).arrow ≫ E.mapOf H


noncomputable def InvSystem.Sub.invSystem [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) :
  InvSystem I 𝓒
where
  obj i := Subobject.underlying.obj (S.hom (unop i))
  map {i j} f := S.map f.unop.down.down
  map_id := by
    intro i
    refine Subobject.eq_of_comp_arrow_eq_iff.mpr ?_
    rw [S.fac (le_refl (unop i))]
    simp
    conv => arg 2; rw [<- Category.comp_id ((S.hom (unop i)).arrow)]
    rfl
  map_comp {i j k} f g := by
    refine Subobject.eq_of_comp_arrow_eq_iff.mpr ?_
    rw [Category.assoc, S.fac (g.unop.down.down)]
    slice_rhs 1 2 => rw [S.fac (f.unop.down.down)]
    rw [S.fac (le_trans (g.unop.down.down) (f.unop.down.down))]
    simp
    rw [<- mapOf_comp]

noncomputable def InvSystem.Sub.incl [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) :
  S.invSystem ⟶ E
where
  app i := (S.hom i.unop).arrow
  naturality {i j} f := S.fac f.unop.down.down

noncomputable def InvSystem.Sub.limMap [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit S.invSystem] :
  S.invSystem.limit ⟶ E.limit
:= InvSystem.limMap S.incl

lemma InvSystem.Sub.limMap_mono [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : E.Sub) [HasLimit E] [HasLimit S.invSystem] :
  Mono (S.limMap)
:= by
  constructor; intro X f g H
  apply InvSystem.hom_ext
  intro i
  apply (S.hom i).arrow_mono.right_cancellation
  rw [Category.assoc, Category.assoc]
  simp [InvSystem.π]
  have E1 := Limits.limMap_π (S.incl) (op i)
  change S.limMap  ≫ E.π i = limit.π S.invSystem (op i) ≫ S.incl.app (op i) at E1
  simp [InvSystem.Sub.incl] at E1
  grind


noncomputable def InvSystem.subobject [Preorder I] [Category 𝓒] [HasPullbacks 𝓒] :
  (InvSystem I 𝓒)ᵒᵖ ⥤ I ⥤ Type
where
  obj E := {
    obj i := Subobject (E.unop.proj (op i))
    map {i j} f := (Subobject.pullback (E.unop.map (op f))).obj
    map_id := by
      intro i
      conv => arg 1; arg 1; arg 1; arg 2; change (𝟙 i).op
      funext x; simp
      rw [Subobject.pullback_id]
    map_comp {i j k} f g:= by
      funext x; simp
      conv => arg 1; arg 1; arg 1; arg 2; change (f ≫ g).op
      simp
      rw [Subobject.pullback_comp]
      conv => arg 2; arg 1; arg 1; arg 2; change g.op
      conv => arg 2; arg 2; arg 1; arg 1; arg 2; change f.op
  }
  map {E F} u := {
    app i := (Subobject.pullback (u.unop.app (op i))).obj
    naturality := by
      intro i j f; simp
      have Hf := u.unop.naturality (op f)
      funext x; simp
      rw [<-  Subobject.pullback_comp,  <- Subobject.pullback_comp, Hf]
  }
  map_id := by
    intro E; simp
    apply NatTrans.ext; simp
    funext i; simp
    funext x; simp
    rw [Subobject.pullback_id]
  map_comp {E F J} u v:= by
    apply NatTrans.ext; simp
    funext i; simp
    funext x; simp
    rw [Subobject.pullback_comp]


def Sub [Preorder I] [Category 𝓒] (E : InvSystem I 𝓒) := Subobject E

noncomputable def Sub.invSystem [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : Sub E) :
  InvSystem I 𝓒
:= Subobject.underlying.obj S

lemma Sub.naturality [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : Sub E) {i j : Iᵒᵖ} (f : i ⟶ j) :
  S.invSystem.map f ≫ S.arrow.app j = S.arrow.app i ≫ E.map f
:= S.arrow.naturality f

noncomputable def Sub.limMap [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : Sub E) [HasLimit E] [HasLimit S.invSystem] :
  S.invSystem.limit ⟶ E.limit
:= InvSystem.limMap S.arrow

lemma Sub.limMap_mono [Preorder I] [Category 𝓒] {E : InvSystem I 𝓒} (S : Sub E) [HasLimit E] [HS : HasLimit S.invSystem] :
  Mono (S.limMap)
:= by
  unfold Sub.limMap InvSystem.limMap
  simp [Sub.invSystem] at HS
  have : ∀ (j : Iᵒᵖ), Mono ((Subobject.arrow S).app j) := by {
    intro i; constructor; intro X f g H
    #check S.arrow_mono.right_cancellation


  }


  #check Limits.limMap_mono (α := S.arrow)
  constructor; intro X f g H
  apply InvSystem.hom_ext
  intro i
  #check S.arrow_mono.right_cancellation
  apply (S.hom i).arrow_mono.right_cancellation
  rw [Category.assoc, Category.assoc]
  simp [InvSystem.π]
  have E1 := Limits.limMap_π (S.incl) (op i)
  change S.limMap  ≫ E.π i = limit.π S.invSystem (op i) ≫ S.incl.app (op i) at E1
  simp [InvSystem.Sub.incl] at E1
  grind




































































end Bourbaki
