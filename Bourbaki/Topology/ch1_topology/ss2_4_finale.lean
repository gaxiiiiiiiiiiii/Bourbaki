import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous
import Bourbaki.Topology.ch1_topology.ss2_3_subbasis

namespace Bourbaki

section Def

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
    apply (HY i).isOpen_union; simp
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




































end Def
