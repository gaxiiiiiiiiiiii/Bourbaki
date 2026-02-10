import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous
import Bourbaki.Topology.ch1_topology.ss2_3_subbasis
import Bourbaki.Topology.ch1_topology.ss2_3_init
import Bourbaki.Topology.ch1_topology.ss2_4_finale

namespace Bourbaki

structure GlueData where
  L : Type _
  f : L → Type _
  A : ∀ (l n : L), Set (f l)
  h : ∀ (n l : L), A l n → A n l
  A_mem : ∀ l x, x ∈ A l l
  h_idem : ∀ l x, h l l x = x
  h_mem : ∀ (l n m : L) (x : A l n) (Hx : x.1 ∈ A l m), (h n l x).1 ∈ A n m
  cocycle : ∀ (l n m : L) (x : A l n) (Hx : x.1 ∈ A l m),
    (h m l ⟨x.1, Hx⟩).1 = (h m n ⟨h n l x, h_mem l n m x Hx⟩).1


def GlueData.equiv (G : GlueData) (l n : G.L) : G.A l n ≃ G.A n l
where
  toFun := G.h n l
  invFun := G.h l n
  left_inv := by
    intro ⟨x, Hx⟩
    have Hxl := G.A_mem l x
    have Hl := G.cocycle l n l ⟨x, Hx⟩ Hxl
    have := G.h_idem l ⟨x, Hxl⟩
    grind
  right_inv := by
    intro ⟨x, Hx⟩
    have Hxn := G.A_mem n x
    have Hn := G.cocycle n l n ⟨x, Hx⟩ Hxn
    have := G.h_idem n ⟨x, Hxn⟩
    grind

def GlueData.setoid (G : GlueData) : Setoid (Σ i, G.f i)
where
  -- r ⟨l, x⟩ ⟨n, y⟩ := y ∈ A n l ∧ x ∈ A l n ∧ h n l ⟨x, _⟩ = y
  r x y := y.snd ∈ G.A y.fst x.fst ∧ ∃ (Hx : x.snd ∈ G.A x.fst y.fst), (G.h y.fst x.fst ⟨x.snd, Hx⟩).1 = y.snd
  iseqv := {
    refl := by
      intro ⟨l, x⟩; simp
      use (G.A_mem l x)
      rw [G.h_idem l]
    symm := by
      intro ⟨l, x⟩ ⟨n, y⟩; simp
      intro Hy Hx E
      use Hx, Hy
      have := (G.equiv n l).right_inv ⟨x, Hx⟩
      have := congr_arg Subtype.val this
      conv at this => arg 2; simp
      rw [<- this]
      simp only [GlueData.equiv]
      have : G.h n l ⟨x, Hx⟩ = ⟨y, Hy⟩ := by ext; rw [E]
      rw [this]
    trans := by
      intro ⟨l, x⟩ ⟨n, y⟩ ⟨m, z⟩; simp
      intro Hy Hx Ey Hz Hy' Ez
      have Hz' := G.h_mem n m l ⟨y, Hy'⟩ Hy
      rw [Ez] at Hz'; use Hz'
      have := G.h_mem n l m ⟨y, Hy⟩ Hy'
      have Hhx : ↑(G.h n l ⟨x, Hx⟩) ∈ G.A n l := by rw [Ey]; grind
      have E : (⟨y, Hy⟩ : { x // x ∈ G.A n l }) = ⟨↑(G.h n l ⟨x, Hx⟩), Hhx⟩ := by ext; simp; rw [Ey]
      rw [E] at this; clear E
      have E := (GlueData.equiv G l n).left_inv ⟨x, Hx⟩
      simp only [GlueData.equiv] at E
      have Ex := congr_arg Subtype.val E; simp at Ex
      have E' : ↑(G.h l n ⟨↑(G.h n l ⟨x, Hx⟩), Hhx⟩) = ↑(G.h l n (G.h n l ⟨x, Hx⟩)) := by ext; simp
      rw [E', Ex] at this
      use this
      have Hhx' : ↑(G.h n l ⟨x, Hx⟩) ∈ G.A n m := by grind
      have Ey' : (⟨y, Hy'⟩ : { x // x ∈ G.A n m }) = ⟨↑(G.h n l ⟨x, Hx⟩), Hhx'⟩  := by ext; simp; grind
      rw [Ey'] at Ez
      have := G.cocycle l n m ⟨x, Hx⟩ this
      rw [this, <- Ez]
  }

lemma GlueData.classes_singleton (G : GlueData) :
  ∀ S ∈ (G.setoid).classes, ∀ l, (Sigma.mk l ⁻¹' S).Subsingleton
:= by
  intro S HS l x Hx y Hy
  simp at *
  simp [Setoid.classes] at HS
  rcases HS with ⟨n, z, rfl⟩
  simp at *
  have := (G.setoid).trans Hx ((G.setoid).symm Hy)
  simp [HasEquiv.Equiv, GlueData.setoid] at this
  rcases this with ⟨Ay, Ax, E⟩
  rw [G.h_idem l] at E; simp at E
  exact E

lemma GlueData.ext (G : GlueData) {l : G.L} (x y : G.f l) :
  (⟦⟨l, x⟩⟧ : Quotient G.setoid )= ⟦⟨l, y⟩⟧ →  x = y
:= by
  intro H;
  apply G.classes_singleton {k | G.setoid k ⟨l, x⟩}
  · apply Setoid.mem_classes
  · simp; apply G.setoid.refl
  · simp
    rw [Quotient.eq] at H
    apply G.setoid.symm H

lemma GlueData.A_eq (G : GlueData) (l n : G.L) :
  G.A l n = {x : G.f l | ∃ y : G.f n , G.setoid.r ⟨l, x⟩ ⟨n, y⟩}
:= by
  ext x; simp [GlueData.setoid]
  constructor; swap; grind
  intro Hx
  have := G.h_mem l n l ⟨x, Hx⟩ (G.A_mem l x)
  use G.h n l ⟨x, Hx⟩, this; simp; assumption

lemma GlueData.A_eq' (G : GlueData) (l n : G.L) :
  G.A l n = ⋃ y : G.f n, (Sigma.mk l) ⁻¹' {x | G.setoid.r x ⟨n, y⟩}
:= by rw [G.A_eq]; ext x; simp

noncomputable def GlueData.mk' {L : Type _} (f : L → Type _)(R : Setoid (Σ i, f i)) (HR : ∀ S ∈ R.classes, ∀ l, (Sigma.mk l ⁻¹' S).Subsingleton) :
  GlueData
where
  L := L
  f := f
  A l n := {x : f l | ∃ y : f n, R ⟨l, x⟩ ⟨n, y⟩}
  h n l := fun x => ⟨x.2.choose, ⟨x.1, R.symm x.2.choose_spec⟩⟩
  A_mem l x := by use x
  h_idem l x := by
    rcases x with ⟨x, Hx⟩; simp
    set y := Hx.choose
    apply HR {y | R y ⟨l, x⟩}<;> try simp
    · apply R.mem_classes
    · apply R.symm Hx.choose_spec
    · apply R.refl
  h_mem l n m x H := by
    rcases x with ⟨x, Hx⟩; simp
    have Hy := Hx.choose_spec
    set y := Hx.choose
    rcases H with ⟨y', Hy'⟩; simp at Hy'
    use y'
    apply R.trans (R.symm Hy) Hy'
  cocycle l n m x H2 := by
    rcases x with ⟨x, H1⟩; simp at H1 H2 ⊢
    have Hy := H1.choose_spec
    set y := H1.choose
    have Hz := H2.choose_spec
    set z := H2.choose
    apply HR {y | R y ⟨m, z⟩}
    · apply R.mem_classes
    · simp; apply R.refl
    · simp
      have Hy' : y ∈ {x | ∃ y, R ⟨n, x⟩ ⟨m, y⟩} := by
        simp; use z, R.trans (R.symm Hy) Hz
      have Ha := Hy'.choose_spec
      set a := Hy'.choose
      apply R.trans (R.symm Ha)
      apply R.trans (R.symm Hy) Hz


def GlueData.quotient (G : GlueData) := Quotient (G.setoid)

def GlueData.φ (G : GlueData) : (Σ l, G.f l) → G.quotient := Quotient.mk (G.setoid)

def GlueData.ι (G : GlueData) (l : G.L) : G.f l → G.quotient :=  Quotient.mk (G.setoid) ∘ Sigma.mk l

lemma GlueData.range_eq (G : GlueData) (l : G.L) :
  Set.range (G.ι l) = ⋃ y : G.f l, Quotient.out ⁻¹' {x | G.setoid ⟨l, y⟩ x}
:= by
  ext x; simp [GlueData.ι]
  constructor<;> intro Hx
  · rcases Hx with ⟨y, Hy⟩
    use y
    change G.setoid ⟨l, y⟩ x.out
    rw [<- Quotient.eq]
    rw [Hy, Quotient.out_eq x]
  · rcases Hx with ⟨y, (Hy : G.setoid ⟨l, y⟩ x.out)⟩
    rw [<- Quotient.eq] at Hy
    use y
    rw [<- Quotient.out_eq x, Hy]


lemma GlueData.ι_injective (G : GlueData) (l : G.L):
  (G.ι l).Injective
:= by
  intro x y E
  simp [GlueData.ι] at E
  apply G.ext x y E

noncomputable def GlueData.ι_equiv (G : GlueData) (l : G.L) :
  G.f l ≃ ↑(Set.range (G.ι l))
:= Equiv.ofInjective _ (G.ι_injective l)

instance GlueData.topology (G : GlueData) [∀ l : G.L, Topology (G.f l)] : Topology (G.quotient) :=
  Finale.topology G.ι

lemma GlueData.isContinuous (G : GlueData) [∀ l : G.L, Topology (G.f l)] :
  ∀ l, IsContinuous (G.ι l)
:= Finale.isContinuous G.ι

instance GlueData.sum (G : GlueData) [∀ l : G.L, Topology (G.f l)] : Topology (Σ i, G.f i) := Finale.sum G.f

def GlueData.topology' (G : GlueData) [∀ l : G.L, Topology (G.f l)] : Topology (G.quotient) :=
  Finale.quotient G.setoid

lemma GlueData.topology_eq_topology' (G : GlueData) [∀ l : G.L, Topology (G.f l)] :
  G.topology = G.topology'
:= by
  unfold GlueData.topology GlueData.topology' Finale.quotient
  apply le_antisymm<;> apply Finale.finale_le<;>
  intro i<;> rw [@IsContinuous_iff]<;>
  intro U HU
  · induction HU with
    | base V HV =>
      simp [Finale.base, Finale.to] at HV
      change  G.sum.isOpen _ at HV
      rw [Finale.sum.isOpen_iff] at HV
      simp [GlueData.ι, Set.preimage_comp]
      exact HV i
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IH =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at *
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_sUnion
      intro T HT; simp at HT
      rcases HT with ⟨SV, rfl⟩
      apply IH _ SV
  · rw [Finale.sum.isOpen_iff]
    intro i
    induction HU with
    | base V HV =>
      simp [Finale.base, Finale.to] at HV
      apply HV i
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IH =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at *
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_sUnion
      intro T HT; simp at HT
      rcases HT with ⟨SV, rfl⟩
      apply IH _ SV


instance (G : GlueData) [Hf : ∀ l : G.L, Topology (G.f l)] :
  ∀ l, Topology (Set.range (G.ι l))
:= fun l => {
  isOpen U := U ∈ (fun u => (G.ι_equiv l) '' u) '' (Hf l).isOpen
  isOpen_univ := by
    simp
    use Set.univ; simp
    apply Topology.isOpen_univ
  isOpen_inter := by
    intro S T HS HT; simp at *
    rcases HS with ⟨s, Hs, rfl⟩
    rcases HT with ⟨t, Ht, rfl⟩
    use s ∩ t; constructor
    · apply Topology.isOpen_inter _ _ Hs Ht
    · ext x; simp
  isOpen_sUnion := by
    intro S HS; simp at *
    choose f Hf1 Hf2 using HS
    let U := ⋃ s : S , f s.val s.prop
    use U; constructor
    · simp [U]
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨V, HV, rfl⟩
      apply Topology.isOpen_sUnion
      intro W HW; simp at HW
      rcases HW with ⟨VS, rfl⟩
      apply Hf1
    ·
      ext x; simp only [U]
      rw [Set.image_iUnion]
      simp only [Set.mem_iUnion]
      conv => arg 2; simp
      constructor<;> intro Hx
      · grind
      · rcases Hx with ⟨s, Hs, xs⟩
        use ⟨s, Hs⟩
        rw [Hf2]; simp; grind
}

def GlueData.topology'' (G : GlueData)[(l : G.L) → Topology (G.f l)] :
  Topology (G.quotient)
:=  Finale.topology (fun l => (G.ι l ∘ (G.ι_equiv l).symm))

lemma GlueData.topology_eq_topology'' (G : GlueData) [∀ l : G.L, Topology (G.f l)] :
  G.topology = G.topology''
:= by
  unfold GlueData.topology GlueData.topology''
  apply le_antisymm<;> apply Finale.finale_le<;>
  intro l<;> rw [@IsContinuous_iff]<;> intro U HU
  · conv => arg 1; arg 1; change G.ι l
    induction HU with
    | base U HU =>
      simp [Finale.base, Finale.to] at HU
      specialize HU l
      unfold Topology.isOpen instTopologyElemQuotientRangeFι at HU
      simp at HU
      rcases HU with ⟨S, HS, E⟩
      rw [Set.preimage_comp] at E
      symm at E; rw [Set.preimage_eq_iff_eq_image] at E; simp at E
      rw [E]; assumption
      apply Equiv.bijective
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IH =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at *
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨SV, rfl⟩
      apply IH V SV
  · induction HU with
    | base U HU =>
      simp [Finale.base, Finale.to] at HU
      specialize HU l
      use (G.ι l)⁻¹' U, HU
      ext x; simp
    | univ =>
      simp; use Set.univ; simp
      apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      rcases IHS with ⟨S', HS', ES⟩
      rcases IHT with ⟨T', HT', ET⟩
      simp at *
      rw [<- ES, <- ET]
      apply Topology.isOpen_inter<;>
      unfold Topology.isOpen instTopologyElemQuotientRangeFι<;>simp<;> assumption
    | union S HS IH =>
      simp; apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_sUnion
      intro s Hs; simp at Hs
      rcases Hs with ⟨SV, rfl⟩
      apply IH V SV


instance (G : GlueData) [Hf : ∀ l, Topology (G.f l)] (l n : G.L) :
  Topology (G.A l n)
:= Init.induced (Function.Embedding.subtype (G.A l n))


lemma GlueData.range_mem (G : GlueData) [Hf : ∀ l, Topology (G.f l)] (HA : ∀ l n, G.A l n ∈ (Hf l).isOpen):
  ∀ l, Set.range (G.ι l) ∈ G.topology.isOpen
:= by
  intro l
  unfold Topology.isOpen GlueData.topology
  apply GenedOpen.base; simp only [Finale.base, Finale.to]
  intro i
  simp [GlueData.ι]
  rw [Set.range_comp, Set.preimage_comp]
  have : Sigma.mk i ⁻¹' (Quotient.mk G.setoid ⁻¹' (Quotient.mk G.setoid '' Set.range (Sigma.mk l))) = G.A i l := by {
    ext x; simp
    rw [G.A_eq]; simp
    constructor<;> intro ⟨y, Hy⟩<;> use y
    · rw [Quotient.eq] at Hy
      apply G.setoid.symm Hy
    · rw [Quotient.eq]
      apply G.setoid.symm Hy
  }
  rw [this]
  apply HA

noncomputable def GlueData.Homeomorphic (G : GlueData) [Hf : ∀ l, Topology (G.f l)]  l :
 Homeomorphic  (G.f l) (Set.range (G.ι l))
where
  toFun := G.ι_equiv l
  invFun := (G.ι_equiv l).invFun
  left_inv := (G.ι_equiv l).left_inv
  right_inv := (G.ι_equiv l).right_inv
  continuous_fun := by
    intro U HU
    unfold Topology.isOpen instTopologyElemQuotientRangeFι at HU; simp at HU
    rcases HU with ⟨V, HV, rfl⟩
    rw [@Equiv.preimage_image]
    exact HV
  continuous_inv := by
    intro U HU
    unfold Topology.isOpen instTopologyElemQuotientRangeFι; simp
    use U, HU
    apply Equiv.image_eq_preimage_symm
