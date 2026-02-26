-- https://www.math.s.chiba-u.ac.jp/~matsu/math/limit.pdf
import Mathlib.tactic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Subobject.MonoOver


open CategoryTheory
open Opposite
open Limits

namespace Bourbaki

abbrev InvSystem (I 𝓒) [SmallCategory I] [Category 𝓒] := Iᵒᵖ ⥤ 𝓒

noncomputable abbrev InvSystem.limit {I 𝓒} [SmallCategory I] [Category 𝓒] (S : InvSystem I 𝓒) [HasLimit S] : 𝓒 := Limits.limit S

lemma InvSystem.limMap_comp
  [SmallCategory I] [Category 𝓒] {E F G : InvSystem I 𝓒}
  [HasLimit E] [HasLimit F] [HasLimit G]
  (u : E ⟶ F) (v : F ⟶ G) :
  limMap (u ≫ v) = limMap u ≫ limMap v
:= by
  apply limit.hom_ext
  intro i; simp




abbrev SubIndex I [SmallCategory.{u} I] :=
  MonoOver (Cat.of.{u, u} I)


abbrev SubIndex.index [SmallCategory I] (J : SubIndex I) := Bundled.α J.obj.left

instance SubIndex.smallCategory_index [SmallCategory I] (J : SubIndex  I) :
  SmallCategory J.index := J.obj.left.str


abbrev SubIndex.functor [SmallCategory I] (J : SubIndex I) :
  J.index ⥤ I
:= J.arrow.toFunctor

abbrev SubIndex.mono [SmallCategory I] (J : SubIndex I) :
  Mono J.arrow
:= J.mono_obj_hom

abbrev InvSystem.restrict [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) (J : SubIndex I) :
  InvSystem J.index 𝓒
:= J.functor.op ⋙ E

noncomputable def InvSystem.restrict.limMap [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) (J : SubIndex I) [HasLimit E] [HasLimit (E.restrict J)] :
  E.limit ⟶ (E.restrict J).limit
:= by
  let c : Cone (E.restrict J) := {
    pt := E.limit
    π := {
      app i := by
        simp
        exact limit.π E (op (J.functor.obj (unop i)))
      naturality {i j} f := by simp
    }
  }
  exact limit.lift (E.restrict J) c

noncomputable def InvSystem.restrict.lmMap
  [SmallCategory I] [Category 𝓒] (E : InvSystem I 𝓒) {J K : SubIndex I}
  [HasLimit (E.restrict J)] [HasLimit (E.restrict K)]
  (u : J ⟶ K) :
  (E.restrict K).limit ⟶ (E.restrict J).limit
:= by

  have Hw := u.hom.w
  conv at Hw => arg 1; arg 1; simp
  conv at Hw => arg 2; simp
  let σ := (eqToHom Hw.symm).toNatTrans



  let c : Cone (E.restrict J) := {
    pt := (E.restrict K).limit
    π := {
      app j := limit.π (E.restrict K) (op ((u.hom.left).toFunctor.obj j.unop)) ≫ E.map (σ.app j.unop).op

      naturality {j j'} f := by
        simp
        let f' := u.hom.left.toFunctor.map f.unop
        have Hw := limit.w (E.restrict K) f'.op
        rw [<- Hw]; clear Hw; simp
        rw [<- CategoryTheory.Functor.map_comp, <- CategoryTheory.Functor.map_comp]
        rw [<- op_comp, <- op_comp]
        suffices : σ.app (unop j') ≫ K.functor.map f' = J.functor.map f.unop ≫ σ.app (unop j)
        rw [this]
        have := σ.naturality f.unop
        simp [SubIndex.functor, MonoOver.arrow]
        grind
    }
  }
  exact  limit.lift (E.restrict J) c


end Bourbaki
