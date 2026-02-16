import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3

namespace Bourbaki
open Classical

instance prod {I : Type _} (f : I → Type _) [HY : ∀ i, Topology (f i)] :
  Topology (Π i, f i)
:= Init.topology (fun i (X : Π i, f i) => X i)

def prod.pr {I : Type _} (X : I → Type _) (i : I) :
  (Π i, X i) → X i
:= fun f => f i


lemma prod.isOpen_iff {I : Type _} (X : I → Type _) [HX : ∀ i, Topology (X i)] (U : Set (Π i, X i)) :
  U ∈ Topology.isOpen  ↔  (∃ B ⊆ {V | ∃ U : Finset (Set ((i : I) → X i)), ((U : Set (Set (Π i, X i))) ⊆ Init.subbase fun i X ↦ X i) ∧ V = ⋂₀ (U : Set (Set (Π i, X i)))}, U = ⋃₀ B)
:= by
  rw [Init.isOpen_iff]; simp; rfl


lemma prod.isContinuous {I : Type _} (f : I → Type _) [HY : ∀ i, Topology (f i)] :
  ∀ (i : I), IsContinuous fun (X : Π i, f i) ↦ X i
:= Init.isContinuous (fun i (X : Π i, f i) => X i)

def prod.subbase {I : Type _}(X : I → Type _) [HX : ∀ i, Topology (X i)] :
  Set (Set (Π i, X i))
:= Init.subbase (fun i (f : Π i, X i) => f i)

def prod.base {I : Type _}(X : I → Type _) [HX : ∀ i, Topology (X i)] :
  Set (Set (Π i, X i))
:= Init.base (fun i (f : Π i, X i) => f i)

lemma prod.mem_subbase_iff  {I : Type _}(X : I → Type _) [HX : ∀ i, Topology (X i)] :
  ∀ f, f ∈ prod.subbase X ↔ ∃ i, ∃ U ∈ Topology.isOpen, f = {g | g i ∈ U}
:= by simp [prod.subbase, Init.subbase, Init.to]; grind


lemma prod.mem_base_iff {I : Type _}(X : I → Type _) [HX : ∀ i, Topology (X i)] :
  ∀ f, f ∈ prod.base X ↔
  ∃ U : Finset (Set (Π i, X i)), ((U : Set (Set (Π i, X i))) ⊆ prod.subbase X) ∧ f = ⋂₀ (U : Set (Set (Π i, X i)))
:= by
  intro f
  simp [base, subbase]
  conv => arg 1; change ∃ U : Finset (Set ((i : I) → X i)), ((U : Set (Set ((i : I) → X i))) ⊆ Init.subbase fun i (f : (i : I) → X i) ↦ f i) ∧ f = ⋂₀ (U : Set (Set ((i : I) → X i)))


lemma prod.isContinuousAt_iff {I : Type _}(X : I → Type _) [HX : ∀ i, Topology (X i)] [HY : Topology Y] (f : Y → Π i, X i) (a : Y) :
  IsContinuousAt f a ↔ ∀ i, IsContinuousAt (fun y => f y i) a
:= by
  rw [Init.IsContinuousAt_iff]
  unfold Function.comp; simp

def prod.lift {I : Type _} {X : I → Type _} {Y : I → Type _} (f : ∀ i, X i → Y i) :
  (Π i, X i) → (Π i, Y i)
:= fun g i => f i (g i)

lemma prod.lift_isContinuousAt {I : Type _} {X : I → Type _} {Y : I → Type _}
  [HX : ∀ i, Topology (X i)] [HY : ∀ i, Topology (Y i)]
  (f : ∀ i, X i → Y i) (a : Π i, X i) :
  IsContinuousAt (lift f) a
  ↔ ∀ i, IsContinuousAt (f i) (a i)
:= by
  rw [isContinuousAt_iff]
  constructor<;> intro H; swap
  · intro i U HU
    specialize H i U HU
    unfold neighborOf NeighborOf at H ⊢; simp at H ⊢
    rcases H with ⟨V, HV, Va, VU⟩
    have HX := isContinuous X i
    rw [IsContinuous_iff] at HX
    specialize HX V HV
    use ((fun X ↦ X i) ⁻¹' V), HX; simp
    use Va
    intro g Hg; simp at Hg ⊢
    apply VU Hg
  · intro i
    let s : X i → Π i, X i := fun x => Function.update a i x
    have Es :  (fun y ↦ lift f y i) ∘ s = f i := by {
      ext x; simp [s, lift]
    }
    rw [<- Es]
    apply IsContinuousAt_comp; swap
    · simp [s]; apply H
    ·
      rw [prod.isContinuousAt_iff]
      intro j; simp [s]
      unfold Function.update
      split_ifs with E
      · subst j; simp
        intro U HU; exact HU
      · intro U HU; simp at *
        have Uj := neighborOf_mem_self HU
        have : (fun (y : X i) ↦ a j) ⁻¹' U = (Set.univ : Set (X i)) := by {
          ext x; simp; exact Uj
        }
        rw [this]
        unfold neighborOf NeighborOf; simp
        use Set.univ; simp
        apply Topology.isOpen_univ




abbrev biProd (X Y : Type u) : Type u
:= Π b, cond b X Y

def biProd.fst {X Y : Type u} (p : biProd X Y) : X := p true
def biProd.snd {X Y : Type u} (p : biProd X Y) : Y := p false

instance [Topology X] [Topology Y] :
  ∀ b, Topology ((fun b => cond b X Y) b)
:= by
  intro b; rcases b<;> assumption

def graph {X Y : Type u} (f : X → Y) (x : X) :{ g : biProd X Y | g false = f (g true) }
:= ⟨fun b => match b with | true => x | false => f x, by simp⟩

lemma isContinuous_iff_isHomeomorphic_graph  {X Y : Type u} [HX : Topology X] [HY : Topology Y] (f : X → Y) :
  IsContinuous f ↔ IsHomeomorphic (graph f)
:= by
  have Ef : biProd.snd ∘ Subtype.val ∘ graph f = f := by {
    ext x; simp [biProd.snd, graph]
  }
  constructor<;> intro H
  · refine {
      continuous := by
        rw [IsContinuous_iff] at ⊢ H
        intro U HU
        rw [Subtopology.isOpen_eq] at HU
        rcases HU with ⟨V, HV, rfl⟩; simp
        induction HV with
        | base W HW =>
          simp [Init.subbase, Init.to] at HW
          rcases HW with ⟨K, HK, rfl⟩ | ⟨K, HK, rfl⟩; simp [graph]
          · apply H at HK
            have : {a | f a ∈ K} = f ⁻¹' K := by {
              ext x; simp
            }
            rw [this]; exact HK
          · simp [graph]; exact HK
        | univ =>
          simp; apply Topology.isOpen_univ
        | inter S T HS HT IHS IHT =>
          simp
          rw [Set.setOf_and]
          apply Topology.isOpen_inter _ _ IHS IHT
        | union S HS IHS =>
          have : {a | (graph f a).val ∈ ⋃₀ S} =  ⋃ s ∈ S, {a | (graph f a).val ∈ s} := by {
            ext x; simp
          }
          rw [this]
          apply Topology.isOpen_sUnion
          intro s Hs; simp at Hs
          rcases Hs with ⟨W, rfl⟩
          apply Topology.isOpen_sUnion
          intro s Hs; simp at Hs
          rcases Hs with ⟨WS, rfl⟩
          apply IHS W WS
      bij := by
        constructor
        · intro x y E
          have := congr_arg (biProd.fst ∘ Subtype.val) E;
          simp [graph, biProd.fst] at this
          exact this
        · intro ⟨p, Hp⟩; simp at Hp
          use p true; simp [graph]
          ext b; rcases b<;> simp
          rw [Hp]
      open_map := by
        intro x U HU
        unfold neighborOf NeighborOf at HU ⊢; simp at HU ⊢
        rcases HU with ⟨V, HV, Vx, VU⟩
        use { g | g.val true ∈ V}
        constructor; swap
        · constructor
          · simp [graph]; exact Vx
          · intro i Hi; simp at Hi; simp
            rcases i with ⟨g, Hg⟩; simp at Hi
            use g true, VU Hi
            ext b; simp [graph]
            rcases b<;> simp; rw [Hg]
        ·
          have Hpr := prod.isContinuous (fun b => cond b X Y) true
          rw [IsContinuous_iff] at Hpr; simp at Hpr
          specialize Hpr V HV

          change ((fun g : Π b, cond b X Y ↦ g true) ⁻¹' V) ∈ Topology.isOpen at Hpr
          rw [Subtopology.isOpen_eq]
          use (fun g ↦ g true) ⁻¹' V, Hpr
          ext g; simp; grind
    }
  · rw [<- Ef]
    apply IsContinuous_comp; apply IsContinuous_comp
    · apply H.continuous
    · apply Subtopology.isContinuous
    · exact prod.isContinuous (fun b => cond b X Y) false


def prod.partition {I K : Type _} {X : I → Type _} {J : K → Set I} (HJ : IndexedPartition J) [HX : ∀ i, Topology (X i)] :
  Homeomorphic (Π i, X i) (Π k : K,  Π i : J k, X i.val)
where
  toFun := fun f k i => f i.val
  invFun := fun g i => g (HJ.index i) ⟨i, HJ.mem_index i⟩
  right_inv := by
    intro f; ext k i; simp
    have E := HJ.eq_of_mem i.prop (HJ.mem_index i)
    grind
  left_inv := by
    intro f; ext i; simp
  continuous_fun := by
    intro U HU
    induction HU with
    | base V HV =>
      simp [Init.subbase, Init.to] at HV
      rcases HV with ⟨k, W, HW, rfl⟩
      induction HW with
      | base S HS =>
        simp [Init.subbase, Init.to] at HS
        rcases HS with ⟨i, Hi, T, HT, rfl⟩
        apply GenedOpen.base
        simp [Init.subbase, Init.to]
        use i, T, HT
        ext g; simp
      | univ =>
        simp; apply Topology.isOpen_univ
      | inter S T HS HT IHS IHT =>
        simp; apply Topology.isOpen_inter _ _ IHS IHT
      | union S HS IHS =>
        simp; apply Topology.isOpen_sUnion
        intro s Hs; simp at Hs
        rcases Hs with ⟨W, rfl⟩
        apply Topology.isOpen_sUnion
        intro s Hs; simp at Hs
        rcases Hs with ⟨H, rfl⟩
        apply IHS W H
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IHS =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨W, rfl⟩
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨H, rfl⟩
      apply IHS W H
  continuous_inv := by
    intro U HU
    induction HU with
    | base V HV =>
      simp [Init.subbase, Init.to] at HV
      rcases HV with ⟨i, W, HW, rfl⟩
      apply GenedOpen.base
      simp [Init.subbase, Init.to]
      use HJ.index i
      use (fun (g : Π i : (J (HJ.index i)), X i) => g ⟨i, HJ.mem_index i⟩) ⁻¹' W
      constructor; swap
      · ext x; simp
      · apply GenedOpen.base
        simp [Init.subbase, Init.to]
        use i, HJ.mem_index i, W, HW
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IHS =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨W, rfl⟩
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨H, rfl⟩
      apply IHS W H


lemma prod.curry {X I : Type _} {Y : I → Type _} [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :
  Init.topology f = Init.inverse (fun x i => f i x)
:= by
  unfold Init.inverse
  have := Init.trans (h := (fun (_ : PUnit.{1}) x i => f i x)) (g := fun (_ : PUnit.{1}) i (g : Π i, Y i) => g i)
  rw [<- this]; clear this
  apply le_antisymm<;> apply Init.le_init
  · intro ⟨u, i⟩; simp
    rw [IsContinuous_iff]
    intro U HU
    have : ((fun g ↦ g i) ∘ fun x i ↦ f i x) = f i := by ext x; simp
    rw [this]; clear this
    apply GenedOpen.base; simp [Init.subbase, Init.to]
    use i, U, HU
  · intro i
    rw [IsContinuous_iff]
    intro U HU
    apply GenedOpen.base; simp [Init.subbase, Init.to]
    use i, U, HU
    ext g; simp

lemma prod.uncurry {X I : Type _} {Y : I → Type _} [HY : ∀ i, Topology (Y i)] (f : X → Π i, Y i) :
  Init.inverse f = Init.topology (fun i x => f x i)
:= by
  set g := (fun i x => f x i)
  have : f = fun x i => g i x := by ext x i; simp [g]
  rw [this, curry]

def subprod {I : Type _} {X : I → Type _} [∀ i, Topology (X i)] :
  (Π i, Set (X i)) → Set (Π i, X i)
:= fun A => Set.univ.pi A


def prod.subprod_homeompophic {I : Type _} {X : I → Type _} [∀ i, Topology (X i)] (A : (i : I) → Set (X i)) :
  Homeomorphic (Π i, A i)  (subprod A)
where
  toFun := fun f => ⟨fun i => (f i).val, by simp [subprod]⟩
  invFun := fun x i => ⟨x.val i, x.prop i (by simp)⟩
  left_inv := by intro x; simp
  right_inv := by intro p; simp
  continuous_fun := by
    intro U HU
    rw [Subtopology.isOpen_eq] at HU
    rcases HU with ⟨V, HV, rfl⟩; simp
    have : {a : (i : I) → (A i) | (fun i ↦ ↑(a i)) ∈ V} = prod.lift (fun i => @Subtype.val (X i) (A i)) ⁻¹' V := by ext x; unfold prod.lift; simp
    rw [this]
    have : IsContinuous (prod.lift (fun i => @Subtype.val (X i) (A i)) : (Π i, A i) → (Π i, X i)) := by {
      intro g
      rw [prod.lift_isContinuousAt]
      intro i
      apply Subtopology.isContinuous (A i) (g i)
    }
    rw [IsContinuous_iff] at this
    apply this V HV
  continuous_inv := by
    intro U (HU : U ∈ Topology.isOpen)
    induction HU with
    | base V HV =>
      simp [Init.subbase, Init.to] at HV
      rcases HV with ⟨i, W, HW, rfl⟩
      rw [<- Set.preimage_comp]
      rw [Subtopology.isOpen_eq] at HW
      rcases HW with ⟨W', HW', rfl⟩; simp
      apply GenedOpen.base
      simp [Init.subbase, Init.to, Function.Embedding.subtype]
      have Hi := prod.isContinuous X i
      rw [IsContinuous_iff] at Hi
      specialize Hi W' HW'
      use ((fun (f : Π i, X i) ↦ f i) ⁻¹' W'), Hi
      ext p; simp
    | univ =>
      simp
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IHS =>
      simp; apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨W, rfl⟩
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨H, rfl⟩
      apply IHS W H

lemma prod.subtopology_eq {I : Type _} {Y : I → Type _} [HY : ∀ i, Topology (Y i)] (A : (i : I) →  Set (Y i)) :
  prod (fun i => A i) = Init.inverse (fun (f : Π i, A i) i => (f i).val)
:= by
  let σ := subprod_homeompophic A
  rw [<- curry (fun i (f : Π i, A i) => (f i).val )]
  simp [prod]
  apply le_antisymm
  · apply Init.le_init
    intro i
    rw [IsContinuous_iff]
    intro U HU
    let g := Subtype.val ∘ (fun f : Π i, A i => f i)
    have E :(fun f : Π i, A i ↦ ↑(f i)) = g := by ext f; simp [g]
    rw [E]
    suffices : IsContinuous g
    rw [IsContinuous_iff] at this
    apply this U HU
    simp [g]
    apply IsContinuous_comp
    · apply prod.isContinuous (fun i => A i) i
    · apply Subtopology.isContinuous
  · apply Init.le_init
    intro i
    have Hi := prod.isContinuous (fun i => A i) i
    rw [IsContinuous_iff] at Hi ⊢
    intro U HU; specialize Hi U HU
    apply σ.continuous_inv at Hi
    rw [Subtopology.isOpen_eq] at Hi
    rcases Hi with ⟨V, HV, E⟩
    simp at E
    rw [Equiv.preimage_eq_iff_eq_image] at E
    rw [E,Equiv.image_symm_eq_preimage]; clear E
    simp [σ,subprod_homeompophic]
    induction HV with
    | base W HW =>
      simp [Init.subbase, Init.to] at HW
      rcases HW with ⟨i, K, HK, rfl⟩; simp
      apply GenedOpen.base
      simp [Init.subbase, Init.to]
      use i, K, HK; ext f; simp
    | univ =>
      simp
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IHS =>
      have : {a : Π i, A i| (fun i ↦ ↑(a i)) ∈ ⋃₀ S} = ⋃ s ∈ S, {a : Π i, A i | (fun i ↦ ↑(a i)) ∈ s} := by ext x; simp
      rw [this]
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨W, rfl⟩
      apply GenedOpen.union
      intro s Hs; simp at Hs
      rcases Hs with ⟨H, rfl⟩
      apply IHS W H
