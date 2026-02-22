-- https://www.math.s.chiba-u.ac.jp/~matsu/math/limit.pdf
import Mathlib
import Mathlib.CategoryTheory.Limits.HasLimits

open CategoryTheory
open Opposite
open Limits


namespace Bourbaki

abbrev InvSystem (I 𝓒) [Preorder I] [Category 𝓒] := Iᵒᵖ ⥤ 𝓒


def InvSystem.proj [Preorder I] [Category 𝓒] (S : InvSystem I 𝓒) := S.obj


def InvSystem.mapOf [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} {i j : I} (H : i ≤ j) :
  S.obj (op j) ⟶ S.obj (op i)
:= S.map (homOfLE H).op

@[simp]
lemma InvSystem.mapOf_id [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} {i : I} :
  S.mapOf (le_refl i) = 𝟙 (S.obj (op i))
:= by simp [mapOf]

lemma InvSystem.mapOf_comp [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} {i j k : I} (Hij : i ≤ j) (Hjk : j ≤ k) :
  S.mapOf (le_trans Hij Hjk) = S.mapOf Hjk ≫ S.mapOf Hij
:= by
  simp [mapOf]; rw [<- S.map_comp]; congr


lemma InvSystem.naturality [Preorder I] [Category 𝓒] {X Y : InvSystem I 𝓒} (σ : X ⟶ Y) {i j : I} (H : i ≤ j) :
  X.mapOf H ≫ σ.app (op i) = σ.app (op j) ≫ Y.mapOf H
:=  σ.naturality (homOfLE H).op


section

variable [Preorder I] [Category 𝓒] (S : InvSystem I 𝓒) [HasLimit S]

noncomputable abbrev InvSystem.limit : 𝓒 := Limits.limit S

noncomputable def InvSystem.π :
  (i : I) → limit S ⟶ S.obj (op i)
:= fun i => Limits.limit.π S (op i)

noncomputable abbrev InvSystem.lift  (c : Cone S) :
  c.pt ⟶ limit S
:= Limits.limit.lift S c

lemma InvSystem.lift_π (c : Cone S) (i : I) :
  S.lift c ≫ S.π i = c.π.app (op i)
:= limit.lift_π c (op i)

lemma InvSystem.w  {i j : I} (H : i ≤ j) :
  S.π j ≫ S.mapOf H  = S.π i
:= limit.w S (homOfLE H).op

lemma InvSystem.hom_ext {X : 𝓒} (f f' : X ⟶ S.limit) (H : ∀ i, f ≫ S.π i = f' ≫ S.π i) :
  f = f'
:= by
  apply limit.hom_ext (F := S) (X := X) (f := f) (f' := f')
  intro i
  exact H (unop i)

end

noncomputable def InvSystem.limMap [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} {T : InvSystem I 𝓒} [HasLimit S] [HasLimit T] (u : S ⟶ T) :
  S.limit ⟶ T.limit
:= Limits.limMap u

lemma InvSystem.limMap_ext [Preorder I] [Category 𝓒] {S : InvSystem I 𝓒} {T : InvSystem I 𝓒} [HasLimit S] [HasLimit T]
  (f f' : S.limit ⟶ T.limit) (H : ∀ (i : I), f ≫ T.π i = f' ≫ T.π i) :
  f = f'
:= hom_ext _ _ _ H



lemma InvSystem.limMap_π
  [Preorder I] [Category 𝓒] {E F : InvSystem I 𝓒}
  [HasLimit E] [HasLimit F]
  (u : E ⟶ F) (i : I) :
  limMap u ≫ F.π i = E.π i ≫ u.app (op i)
:= by simp [limMap, InvSystem.π]


lemma InvSystem.limMap_comp
  [Preorder I] [Category 𝓒] {E F G : InvSystem I 𝓒}
  [HasLimit E] [HasLimit F] [HasLimit G]
  (u : E ⟶ F) (v : F ⟶ G) :
  limMap (u ≫ v) = limMap u ≫ limMap v
:= by
  apply limMap_ext
  intro i
  rw [Category.assoc, limMap_π, limMap_π, <- Category.assoc, limMap_π]
  simp
