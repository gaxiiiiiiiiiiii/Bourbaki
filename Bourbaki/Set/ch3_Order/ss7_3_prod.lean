import Bourbaki.Set.ch3_Order.ss7_1_inverseLimit
import Bourbaki.Set.ch3_Order.ss7_2_map
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.Currying




namespace Bourbaki

open CategoryTheory
open Opposite
open Limits



noncomputable instance {ι : Type _} (I : ι → Type _) [∀ i, SmallCategory (I i)] :
  SmallCategory (∏ᶜ I)
where
  Hom X Y := ∀ i, Pi.π I i X ⟶ Pi.π I i Y
  id X i := 𝟙 (Pi.π I i X)
  comp f g i := f i ≫ g i
  id_comp {X Y} f := by simp



noncomputable def prod.update {ι : Type _} {I : ι → Type _} (X : ∏ᶜ I) (i : ι) (x : I i) : ∏ᶜ I
:= by classical
  let p : (j : ι) → ∏ᶜ I ⟶ I j := fun j X => if E : j = i then by rw [E]; exact x else Pi.π I j X
  exact Pi.lift p X


lemma prod.pi_update_eq
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)]
  (X : ∏ᶜ I) (i : ι) (x : I i) :
  Pi.π I i (prod.update X i x) = x
:= by simp [prod.update]


lemma prod.pi_update_ne
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)]
  (X : ∏ᶜ I) {i j : ι} (h : j ≠ i) (x : I i) :
  Pi.π I j (prod.update X i x) = Pi.π I j X
:= by simp [prod.update, h]


noncomputable def prod.Update {ι : Type _} (I : ι → Type _) [∀ i, Category (I i)] (i : ι) :
  ( ∏ᶜ I × I i) ⥤ ∏ᶜ I
where
  obj p := update p.1 i p.2
  map {p p'} f j := by
    simp only [update, eq_mpr_eq_cast, Types.pi_lift_π_apply]
    split_ifs with E
    · subst j; simp; exact f.2
    · exact f.1 j
  map_id p := by
    simp; funext j
    split_ifs with E
    · subst j; simp
      rw [@cast_eq_iff_heq]
      simp [CategoryStruct.id]
      have : p.2 = Pi.π I i (update p.1 i p.2)  := by simp [update]
      rw [<- this]
    · simp
      rw [@cast_eq_iff_heq]
      simp [CategoryStruct.id]
      have : (Pi.π I j p.1) = (Pi.π I j (update p.1 i p.2)) := by simp [update]; grind
      rw [this]
  map_comp {p p' p''} f g := by
    simp; funext j
    conv => arg 2; simp [CategoryStruct.comp]
    rw [@cast_eq_iff_heq]
    split_ifs with E
    · subst j; simp
      conv => arg 1; rw [<- Category.id_comp f.2]
      apply heq_comp<;> simp [update]
    · simp
      conv => arg 1; simp [CategoryStruct.comp]
      apply heq_comp<;> simp [update]<;> grind

noncomputable def prod.UpdateOf {ι : Type _} {I : ι → Type _} [∀ i, Category (I i)] (i : ι) :
  ∏ᶜ I ⥤ (I i ⥤ ∏ᶜ I)
:= (Functor.curry.obj (Update I i))

noncomputable def prod.UpdateBy {ι : Type _} {I : ι → Type _} [∀ i, Category (I i)]  (i : ι) :
  I i ⥤ (∏ᶜ I ⥤ ∏ᶜ I)
:= (Functor.curry.obj ((CategoryTheory.Prod.swap _ _ ) ⋙ (Update I i)))

lemma prod.pi_UpdateOf
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)]
  (X : ∏ᶜ I) (i : ι) (x : I i):
  Pi.π I i (((prod.UpdateOf i).obj X).obj x) = x
:= by simp [prod.UpdateOf, prod.Update, prod.update]

noncomputable def prod.updateOf_self
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)]
  (i : ι) (X : (∏ᶜ I)) :
  ((prod.UpdateOf i).obj X).obj (Pi.π I i X) =  X
:= by
  simp [prod.UpdateOf, prod.Update, prod.update]
  refine Types.limit_ext_iff.mpr ?_
  intro ⟨j⟩; simp; grind





noncomputable def InvSystem.slice
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)] [Category 𝓒]
  (E : InvSystem (∏ᶜ I) 𝓒) (i : ι )(X : ∏ᶜ I) :
  InvSystem (I i) 𝓒
:= ((prod.UpdateOf i).obj X).op ⋙ E

noncomputable def InvSystem.sliceAt
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)] [Category 𝓒]
  (E : InvSystem (∏ᶜ I) 𝓒) (i : ι) (x : I i) :
  InvSystem (∏ᶜ I) 𝓒
:= ((prod.UpdateBy i).obj x).op ⋙ E

lemma InvSystem.slice_self
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)] [Category 𝓒]
  (E : InvSystem (∏ᶜ I) 𝓒) (i : ι) (X : ∏ᶜ I) :
  (E.slice i X).obj (op (Pi.π I i X)) = E.obj (op X)
:= by
  simp [InvSystem.slice]
  rw [prod.updateOf_self]


noncomputable def InvSystem.limProd
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)] [Category 𝓒] [HasLimits 𝓒]
  (E : InvSystem (∏ᶜ I) 𝓒) (i : ι)
  :
  InvSystem (∏ᶜ I) 𝓒
where
  obj X := limit (E.slice i X.unop)
  map {X Y} f := Limits.limMap ((NatTrans.op ((prod.UpdateOf i).map f.unop)) ◫ (𝟙 E))
  map_id X := by
    apply limit.hom_ext; intro j
    simp [InvSystem.slice]
  map_comp {X Y Z} f g := by
    apply limit.hom_ext; intro j; simp

-- TODO
/-
直積の逆系で、極限を取る順番を入れ替えても同型なのを証明したい。
この形式化が妥当なのかも自信ない。
正しかったとしても、型キャストが鬱陶しいから一旦諦める。
-/
noncomputable def InvSystem.limProd_iso
  {ι : Type _} {I : ι → Type _} [∀ i, SmallCategory (I i)]
  [Category 𝓒] [HasLimits 𝓒]
  (E : InvSystem (∏ᶜ I) 𝓒) (i : ι)
  :
  limit E ≅ limit (E.limProd i)
where
  hom := by
    apply limMap
    refine {
      app X := by
        simp [InvSystem.limProd, InvSystem.slice]
        simp [prod.UpdateOf, prod.Update, prod.update]


        let c : Cone  (E.slice i (unop X)) := {
          pt := E.obj X
          π := {
            app x := by
              simp [InvSystem.slice]
              apply E.map; apply op; simp
              intro j; simp [prod.UpdateOf, prod.Update, prod.update]
              split_ifs with E
              · subst j; simp
                sorry
              · exact 𝟙 _
            naturality := by
              simp
              sorry
          }
        }
        apply limit.lift _ c
      naturality := by
        sorry
    }
  inv := by
    apply limMap
    refine {
      app X := by
        simp [InvSystem.limProd]
        apply limit.π (E.slice i (unop X)) (op (Pi.π I i X.unop)) ≫ eqToHom (E.slice_self i X.unop)
      naturality {X Y} f := by
        simp [InvSystem.limProd]
        have Ef := limit.w (E.slice i (unop X)) (f.unop i).op
        rw [<- Ef, Category.assoc]
        apply eq_of_heq
        apply heq_comp<;> try rfl
        sorry
    }
