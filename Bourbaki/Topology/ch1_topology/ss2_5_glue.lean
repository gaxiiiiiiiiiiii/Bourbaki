import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous
import Bourbaki.Topology.ch1_topology.ss2_3_subbasis
import Bourbaki.Topology.ch1_topology.ss2_3_init
import Bourbaki.Topology.ch1_topology.ss2_4_finale

namespace Bourbaki

structure Glue where
  L : Type _
  f : L → Type _
  A : ∀ (l n : L), Set (f l)
  h : ∀ (n l : L), A l n → A n l
  A_mem : ∀ l x, x ∈ A l l
  h_idem : ∀ l x, h l l x = x
  h_mem : ∀ (l n m : L) (x : A l n) (Hx : x.1 ∈ A l m), (h n l x).1 ∈ A n m
  cocycle : ∀ (l n m : L) (x : A l n) (Hx : x.1 ∈ A l m),
    (h m l ⟨x.1, Hx⟩).1 = (h m n ⟨h n l x, h_mem l n m x Hx⟩).1


def Glue.equiv (G : Glue) (l n : G.L) : G.A l n ≃ G.A n l
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

def Glue.setoid (G : Glue) : Setoid (Σ i, G.f i)
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
      simp only [Glue.equiv]
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
      have E := (Glue.equiv G l n).left_inv ⟨x, Hx⟩
      simp only [Glue.equiv] at E
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

lemma Glue.setoid.classes_singleton (G : Glue) :
  ∀ S ∈ (G.setoid).classes, ∀ l, (Sigma.mk l ⁻¹' S).Subsingleton
:= by
  intro S HS l x Hx y Hy
  simp at *
  simp [Setoid.classes] at HS
  rcases HS with ⟨n, z, rfl⟩
  simp at *
  have := (G.setoid).trans Hx ((G.setoid).symm Hy)
  simp [HasEquiv.Equiv, Glue.setoid] at this
  rcases this with ⟨Ay, Ax, E⟩
  rw [G.h_idem l] at E; simp at E
  exact E


lemma Glue.A_eq (G : Glue) (l n : G.L) :
  G.A l n = {x : G.f l | ∃ y : G.f n , G.setoid.r ⟨l, x⟩ ⟨n, y⟩}
:= by
  ext x; simp [Glue.setoid]
  constructor; swap; grind
  intro Hx
  have := G.h_mem l n l ⟨x, Hx⟩ (G.A_mem l x)
  use G.h n l ⟨x, Hx⟩, this; simp; assumption


noncomputable def Glue.mk' {L : Type _} (f : L → Type _)(R : Setoid (Σ i, f i)) (HR : ∀ S ∈ R.classes, ∀ l, (Sigma.mk l ⁻¹' S).Subsingleton) :
  Glue
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


def Glue.quotient (G : Glue) := Quotient (G.setoid)

def Glue.quotient_mk (G : Glue) : (Σ l, G.f l) → G.quotient := Quotient.mk (G.setoid)

lemma Glue.inj (G : Glue) (l : G.L):
  (G.quotient_mk ∘ Sigma.mk l).Injective
:= by
  intro x y E
  simp [Glue.quotient_mk] at E
  rw [Quotient.eq, Glue.setoid] at E; simp at E
  rcases E with ⟨Hy, Hx, E⟩
  rw [G.h_idem l] at E; simp at E
  rw [E]

instance Glue.topology (G : Glue) [∀ l : G.L, Topology (G.f l)] : Topology (G.quotient) :=
  Finale.topology (fun l => G.quotient_mk ∘ Sigma.mk l)

instance Glue.sum (G : Glue) [∀ l : G.L, Topology (G.f l)] : Topology (Σ i, G.f i) := Finale.sum G.f


def Glue.topology' (G : Glue) [∀ l : G.L, Topology (G.f l)] : Topology (G.quotient) :=
  Finale.quotient G.setoid

lemma Glue.topology_eq_topology' (G : Glue) [∀ l : G.L, Topology (G.f l)] :
  G.topology = G.topology'
:= by
  unfold Glue.topology Glue.topology' Finale.quotient
  apply le_antisymm<;> apply Finale.finale_le<;>
  intro i<;> rw [@IsContinuous_iff_IsOpen_preimage]<;>
  intro U HU
  · induction HU with
    | base V HV =>
      simp [Finale.base, Finale.to] at HV
      change  G.sum.isOpen _ at HV
      rw [Finale.sum.isOpen_iff] at HV
      grind
    | univ =>
      simp; apply Topology.isOpen_univ
    | inter S T HS HT IHS IHT =>
      simp; apply Topology.isOpen_inter _ _ IHS IHT
    | union S HS IH =>
      simp; apply Topology.isOpen_union
      intro s Hs; simp at *
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_union
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
      simp; apply Topology.isOpen_union
      intro s Hs; simp at *
      rcases Hs with ⟨V, rfl⟩
      apply Topology.isOpen_union
      intro T HT; simp at HT
      rcases HT with ⟨SV, rfl⟩
      apply IH _ SV
