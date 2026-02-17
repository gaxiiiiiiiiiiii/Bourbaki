import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3
import Bourbaki.Topology.ch1_topology.ss4_1_prod
import Bourbaki.Topology.ch1_topology.ss4_1_prod'

namespace Bourbaki
open Classical


lemma prod.update_isContinuous {I : Type _} {X : I → Type _} [∀ i, Topology (X i)] (f : Π i, X i) (i : I) :
  IsContinuous (Function.update f i)
:= by
  rw [IsContinuous_iff]
  intro U HU
  induction HU with
  | base V HV =>
    simp [Init.subbase, Init.to] at HV
    rcases HV with ⟨j, B, HB, rfl⟩
    conv => arg 1; arg 2; arg 1; change prod.pr X j
    by_cases E : j = i
    · subst j
      have : (Function.update f i ⁻¹' (prod.pr X i ⁻¹' B)) = B := by {
        ext x; unfold Function.update prod.pr; simp
      }
      rw [this]; exact HB
    · unfold prod.pr
      by_cases HB : f j ∈ B
      · have : (Function.update f i ⁻¹' ((fun f ↦ f j) ⁻¹' B)) = Set.univ := by
          ext x; simp; unfold Function.update; simp [E]; assumption
        rw [this]; apply Topology.isOpen_univ
      · have : (Function.update f i ⁻¹' ((fun f ↦ f j) ⁻¹' B)) = ∅ := by
          ext x; simp; unfold Function.update; simp [E]; assumption
        rw [this]; apply Topology.isOpen_empty
  | univ =>
    simp; apply Topology.isOpen_univ
  | inter S T HS HT IHS IHT =>
    simp; apply Topology.isOpen_inter _ _ IHS IHT
  | union S H IH =>
    simp; apply Topology.isOpen_sUnion
    intro s Hs; simp at Hs
    rcases Hs with ⟨y, Hy, rfl⟩
    apply Topology.isOpen_sUnion
    intro t Ht; simp at Ht
    rcases Ht with ⟨Hy, rfl⟩
    apply IH y Hy

noncomputable def prod.update_homeomporphic {I : Type _} (X : I → Type _) [HX : ∀ i, Topology (X i)] (f : Π i, X i) (i : I):
  Homeomorphic (X i) (Quotient (Setoid.ker (prod.pr X i)))
where
  toFun x := ⟦Function.update f i x⟧
  invFun x := by
    apply Quotient.liftOn x (prod.pr X i)
    intro g h E
    exact E
  left_inv x := by simp [pr]
  right_inv x := by
    simp; rw [<- Quotient.out_eq x, Quotient.liftOn_mk, pr, Quotient.eq]
    simp [pr]
  continuous_fun := by
    intro U HU
    change U ∈ Topology.isOpen at HU
    rw [Quotspace.isOpen_iff] at HU
    have E : (fun x ↦ (⟦Function.update f i x⟧ :  Quotient (Setoid.ker (pr X i)))) = Quotient.mk (Setoid.ker (pr X i)) ∘ Function.update f i := by { ext x; simp }
    rw [E, Set.preimage_comp]
    have := update_isContinuous f i
    rw [IsContinuous_iff] at this
    apply this _ HU
  continuous_inv := by
    intro U HU
    change ((fun x : Quotient (Setoid.ker (pr X i))↦ x.liftOn (pr X i) (fun _ _ E => E)) ⁻¹' U) ∈ Topology.isOpen
    rw [Quotspace.isOpen_iff]
    apply GenedOpen.base
    simp [Init.subbase, Init.to]
    use i, U, HU; ext g; simp [pr]



noncomputable def prod.update_continuousSection {I : Type _} (X : I → Type _) [HX : ∀ i, Topology (X i)]  (f : Π i, X i) (i : I):
  ContinuousSection (Quotient.mk (Setoid.ker (prod.pr X i)))
where
  sect := Function.update f i ∘ (update_homeomporphic X f i).invFun
  right_inverse := by
    ext x; simp [update_homeomporphic]
    rw [<- Quotient.out_eq x, Quotient.liftOn_mk, Quotient.eq]
    simp [pr]
  continuous := by
    apply IsContinuous_comp
    · rw [IsContinuous_iff]
      exact (update_homeomporphic X f i).continuous_inv
    · apply update_isContinuous f i


lemma prod.slice_isOpen {I : Type _} {X : I → Type _} [∀ i, Topology (X i)] (f : Π i, X i) (U : Set (Π i, X i)) :
  U ∈ Topology.isOpen → ∀ i, {g : X i | Function.update f i g ∈ U} ∈ Topology.isOpen
:= by
  intro HU i
  have := prod.update_isContinuous f i
  rw [IsContinuous_iff] at this
  specialize this U HU
  exact this

lemma prod.pr_image_eq_sUnion {I : Type _} (X : I → Type _)  (S : Set (Π i, X i)) :
  ∀ i, (prod.pr X i) '' S = ⋃ f : Π i, X i, {y : X i | Function.update f i y ∈ S}
:= by
  intro i; ext x; simp
  constructor<;> intro H
  · rcases H with ⟨f, Hf, rfl⟩; simp [pr]
    use f; simp; exact Hf
  · rcases H with ⟨f, Hf⟩
    use  Function.update f i x, Hf
    simp [pr]


lemma prod.pr_openMap {I : Type _} (X : I → Type _) [HX : ∀ i, Topology (X i)] (U : Set (Π i, X i)) :
  U ∈ Topology.isOpen → ∀ i, (prod.pr X i) '' U ∈ Topology.isOpen
:= by
  intro HU i
  rw [pr_image_eq_sUnion]
  apply Topology.isOpen_sUnion
  intro s Hs; simp at Hs
  rcases Hs with ⟨g, Hg, rfl⟩
  have := slice_isOpen g U HU i
  apply this

lemma prod.isContinuousAt_pr {I : Type _} {X : I → Type _} [HX : ∀ i, Topology (X i)] [Topology Y]
  (f : (Π i, X i) → Y) (x : Π i, X i) :
  IsContinuousAt f x → ∀ i, IsContinuousAt (f ∘ (Function.update x i)) (x i)
:= by
  intro H i
  apply IsContinuousAt_comp; swap
  · simp; exact H
  · exact update_isContinuous x i (x i)
