import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous
import Bourbaki.Topology.ch1_topology.ss2_3_subbasis
import Bourbaki.Topology.ch1_topology.ss2_3_init

namespace Bourbaki

variable {X ι : Type _} {Y : ι → Type _}

def Finale (_f : ∀ i, Y i → X) := X

def Finale.to (f : ∀ i, Y i → X) (i : ι) : Y i → Finale f := f i

lemma Finale.to_apply (f : ∀ i, Y i → X) (i : ι) (y : Y i) :
  Finale.to f i y = f i y
:= rfl

def Finale.base [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) :=
  {U | ∀ i, Finale.to f i ⁻¹' U ∈ (HY i).isOpen}

instance Finale.topology [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) :
  Topology (Finale f)
:= GenedTopology (Finale.base f)

lemma Finale.base_isTopologicalBase [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) :
  let _Hf := topology f
  IsTopologicalBase (Finale.base f)
:= by
  intro Hf x
  let G : NeighborBase x Set.univ := {
    base := {V | x ∈ V ∧ V ∈ base f}
    base_isNeighbor := by
      intro S HS; simp at HS
      rcases HS with ⟨Sx, HS⟩
      simp [base] at HS
      simp [neighborWithin]
      use S, ?_, Sx, by simp
      apply GenedOpen.base
      simp [base]
      intro i; simp [Finale.to] at *
      apply HS
    cofinal := by
      intro V HV
      simp [neighborWithin] at HV
      rcases HV with ⟨U, HU, Ux, UV⟩
      revert x V
      induction HU with
      | base U HU =>
        intro x V Hx UV
        use U; simp
        use ⟨Hx, HU⟩, UV
      | univ =>
        intro x V Hx UV; simp at *; subst V; simp
        use Set.univ; simp [base]
        intro i; apply (HY i).isOpen_univ
      | inter S T HS HT IHS IHT =>
        simp at *
        intro x V Sx Tx HV
        specialize IHS x S Sx (by simp)
        specialize IHT x T Tx (by simp)
        rcases IHS with ⟨S', ⟨Sx', HS'⟩, SS⟩
        rcases IHT with ⟨T', ⟨Tx', HT'⟩, TT⟩
        use S' ∩ T'; simp
        constructor; constructor; grind
        · simp [base, Finale.to] at *
          intro i
          apply (HY i).isOpen_inter _ _ (HS' i) (HT' i)
        · grind
      | union S HS IHS =>
        simp at *
        intro x V W HW Wx HV
        specialize IHS W HW x W Wx (by simp)
        rcases IHS with ⟨A, HA, AW⟩
        use A, HA
        apply subset_trans AW
        apply HV _ HW
  }
  use G




lemma Finale.isContinuous [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) (i : ι) :
  @IsContinuous _ _ (HY i) (Finale.topology f) (Finale.to f i)
:= by
  simp [Finale.to]
  rw [@IsContinuous_iff_IsOpen_preimage]
  intro U HU
  induction HU with
  | base V HV =>
    simp [base] at HV
    exact HV i
  | univ =>
    simp; apply (HY i).isOpen_univ
  | inter S T HS HT IHS IHT =>
    simp; apply (HY i).isOpen_inter _ _ IHS IHT
  | union S HS IHS =>
    simp
    have : ⋃ t ∈ S, f i ⁻¹' t = ⋃₀ {U | ∃ t ∈ S, U = f i ⁻¹' t} := by ext U; simp
    rw [this]; clear this
    apply (HY i).isOpen_sUnion; simp
    intro x s Hs rfl
    apply IHS s Hs


lemma Finale.finale_le [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) (HX : Topology X) :
  (∀ i, @IsContinuous _ _ _ HX (f i)) → topology f ≤ HX
:= by
  intro Hf U HU
  apply GenedOpen.base
  simp [base, Finale.to] at *
  intro i
  specialize Hf i
  rw [@IsContinuous_iff_IsOpen_preimage] at Hf
  apply Hf U HU

lemma Finale.isContinuous_iff [Topology Z] [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) (g : X → Z) :
  let _HX : Topology X := Finale.topology f
  IsContinuous g ↔ (∀ i, IsContinuous (g ∘ f i))
:= by
  intro HX
  have Hf := Finale.isContinuous f; simp [Finale.to] at Hf
  constructor<;> intro H
  · intro i
    specialize Hf i
    rw [@IsContinuous_iff_IsOpen_preimage] at *
    intro U HU
    specialize H U HU
    specialize Hf _ H
    exact Hf
  · rw [@IsContinuous_iff_IsOpen_preimage]
    intro U HU
    apply GenedOpen.base
    simp [base, Finale.to]
    intro i
    specialize H i
    rw [@IsContinuous_iff_IsOpen_preimage] at H
    apply H U HU

lemma Finale.isClosed_iff [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) (F : Set X) :
  (topology f).isClosed F ↔ ∀ i,  (HY i).isClosed (f i ⁻¹' F)
:= by
  unfold Topology.isClosed
  have Hf := Finale.isContinuous f; simp [Finale.to] at Hf
  constructor<;> intro H
  · intro i
    specialize Hf i
    rw [@IsContinuous_iff_IsOpen_preimage] at Hf
    specialize Hf _ H; simp at Hf
    exact Hf
  · apply GenedOpen.base
    simp [base, Finale.to]
    intro i
    apply H i

lemma Finale.isOpen_iff [HY : ∀ i, Topology (Y i)] (f : ∀ i, Y i → X) (U : Set X) :
  U ∈ (topology f).isOpen ↔ ∀ i,  (HY i).isOpen (f i ⁻¹' U)
:= by
  conv => arg 1; rw [<- compl_compl U]; change (topology f).isClosed Uᶜ
  rw [isClosed_iff]; unfold Topology.isClosed; simp



lemma Finale.trans {X I L : Type _} {Z : I → Type _} {Y : L → Type _} [HZ : ∀ i, Topology (Z i)] (h : ∀ l, Y l → X) (g : ∀ l i, Z i → Y l) :
  let _HY : ∀ l, Topology (Y l) := fun l =>  Finale.topology (g l)
  Finale.topology h = Finale.topology (fun p : L × I => h p.1 ∘ g p.1 p.2)
:= by
  intro HY
  apply le_antisymm
  · apply finale_le
    intro l
    rw [@IsContinuous_iff_IsOpen_preimage]
    intro U HU
    apply GenedOpen.base
    simp [base, Finale.to]
    intro i
    have := Finale.isContinuous ((fun p : L × I => h p.1 ∘ g p.1 p.2))
    simp [Finale.to] at this
    specialize this l i
    rw [@IsContinuous_iff_IsOpen_preimage] at this
    specialize this U HU
    exact this
  · apply finale_le
    intro ⟨l, i⟩; simp
    have Hg := Finale.isContinuous (g l) i
    have Hh := Finale.isContinuous h l;
    rw [@IsContinuous_iff_IsOpen_preimage, Finale.to] at *
    intro U HU
    apply Hh at HU
    apply Hg at HU
    exact HU

instance Finale.quotient [Topology X] (R : Setoid X) :
  Topology (Quotient R)
:= Finale.topology (fun (_ : PUnit.{1}) => Quotient.mk R)

def Finale.sup {X I : Type _} (HX : I → Topology X) :
  Topology X
:= topology (HY := HX) (fun _ x => x)

lemma Finale.sup_le {X I : Type _} (HX : I → Topology X) :
  ∀ H, (∀ i, HX i ≤ H) → sup HX ≤ H
:= by
  intro H HH U HU
  apply GenedOpen.base; simp [base, Finale.to]
  intro i
  apply HH i U HU


lemma Finale.le_sup {X I : Type _} (HX : I → Topology X) :
  ∀ i, HX i ≤ sup HX
:= by
  intro i U HU
  unfold Topology.isOpen sup topology GenedTopology at HU; simp at HU
  induction HU with
  | base V HV =>
    simp [base, Finale.to] at HV
    exact HV i
  | univ =>
    apply (HX i).isOpen_univ
  | inter S T HS HT IHS IHT =>
    apply (HX i).isOpen_inter _ _ IHS IHT
  | union S HS IHS =>
    apply (HX i).isOpen_sUnion; assumption


def Finale.sum {I : Type _} (f : I → Type _) [Hf : ∀ i, Topology (f i)] :
  Topology (Σ i, f i)
:= Finale.topology (fun i => Sigma.mk i)

lemma Finale.sum.isOpen_iff {I : Type _} (f : I → Type _) [Hf : ∀ i, Topology (f i)] (U : Set (Σ i, f i)) :
  (sum f).isOpen U ↔ ∀ i, (Hf i).isOpen (Sigma.mk i ⁻¹' U)
:= by
  constructor<;> intro H
  · intro i
    have Hi := Finale.isContinuous (HY := Hf) (fun i => Sigma.mk i) i
    rw [@IsContinuous_iff_IsOpen_preimage] at Hi
    exact Hi U H
  · apply GenedOpen.base
    simp [base, Finale.to]
    exact H

def Incl {X : Type _} (S T : Set X) (ST : S ⊆ T) :
  S ↪ T
:= by
  use Set.inclusion ST
  intro ⟨x, Hx⟩ ⟨y, Hy⟩ H; grind

lemma Finale.glue {X L : Type} (f : L → Set X) [Hf : ∀ l, Topology (f l)]
  -- f l ∩ f n が、Hf l と Hf n の双方で開集合
  (H1 : ∀ l n, {x : f l | x.val ∈ f n} ∈ (Hf l).isOpen )
  -- f l ∩ f n ↪ f l と f l ∩ f n ↪ f n から誘導される位相は一する
  (H2 : ∀ l n, Init.induced (Incl (f l ∩ f n) (f l) (by simp)) = Init.induced (Incl (f l ∩ f n) (f n) (by simp)))
  :
  let 𝓣 : Topology X := Finale.topology (HY := Hf) (fun _ => Subtype.val)
  ∀ l, f l ∈ 𝓣.isOpen ∧ Init.induced (Function.Embedding.subtype (f l)) = Hf l
:= by
  intro 𝓣 l
  constructor
  · unfold Topology.isOpen 𝓣 topology GenedTopology; simp
    apply GenedOpen.base; simp [base, Finale.to]
    intro n
    apply H1 n l
  · apply le_antisymm; swap
    · unfold Init.induced Init.inverse
      apply Init.le_init; simp
      rw [IsContinuous_iff_IsOpen_preimage]
      intro U HU
      induction HU with
      | base V HV =>
        simp [base, Finale.to] at HV
        specialize HV l
        exact HV
      | univ =>
        simp; apply (Hf l).isOpen_univ
      | inter S T HS HT IHS IHT =>
        simp; apply (Hf l).isOpen_inter _ _ IHS IHT
      | union S HS IHS =>
        simp
        apply (Hf l).isOpen_sUnion; simp
        intro s
        apply (Hf l).isOpen_sUnion; simp
        intro Hs
        apply IHS s Hs
    · intro V HV
      apply GenedOpen.base; simp [Init.subbase, Init.to]
      use Subtype.val '' V
      constructor; swap; grind
      apply GenedOpen.base; simp [base, Finale.to]
      intro n
      specialize H2 l n
      set fl := (Incl (f l ∩ f n) (f l) (by simp))
      set fn := (Incl (f l ∩ f n) (f n) (by simp))
      have Hl := Init.isContinuous (f := fun _ : PUnit.{1} => fl) PUnit.unit
      have Hn := Init.isContinuous (f := fun _ : PUnit.{1} => fn) PUnit.unit
      rw [@IsContinuous_iff_IsOpen_preimage, Init.to] at Hl Hn
      specialize Hl V HV
      change (⇑fl ⁻¹' V) ∈ (Init.induced fl).isOpen at Hl
      rw [H2] at Hl
      rw [Init.isOpen_iff] at Hl ; simp at Hl
      rcases Hl with ⟨B , HB, E⟩
      have : Subtype.val ⁻¹' (Subtype.val '' V) = ⇑fn '' ⋃₀ B := by {
        rw [<- E]
        ext x; simp
        rcases x with ⟨x, Hx⟩; simp
        constructor<;> intro H
        · rcases H with ⟨flx, Vx⟩
          use x, ⟨flx, Hx⟩
          simp [fl, fn, Incl]; assumption
        · rcases H with ⟨y, ⟨Hly, Hny⟩, Hl, Hn⟩
          simp [fl, fn, Incl] at Hl Hn
          subst y
          use Hly, Hl
      }
      rw [this, Set.image_sUnion]; clear this
      apply Topology.isOpen_sUnion; simp
      intro b Hb; apply HB at Hb; simp at Hb
      rcases Hb with ⟨U, HU, rfl⟩
      induction U using Finset.cons_induction_on with
      | empty =>
        simp [fn, Incl]
        apply H1
      | cons x S Fx IH =>
        simp; rw [Set.image_inter]; swap; grind
        apply Topology.isOpen_inter
        · have Hx : x ∈ Finset.cons x S Fx := by grind
          apply HU at Hx; simp [Init.subbase, Init.to] at Hx
          rcases Hx with ⟨V, HV, rfl⟩
          rw [Set.image_preimage_eq_inter_range]
          apply Topology.isOpen_inter _ _ HV
          simp [fn, Incl]
          apply H1
        · apply IH
          intro s Hs
          apply HU; simp; grind
