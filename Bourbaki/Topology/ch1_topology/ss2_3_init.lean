import Mathlib
import Bourbaki.Topology.ch1_topology.ss1_neighbor
import Bourbaki.Topology.ch1_topology.ss2_continuous
import Bourbaki.Topology.ch1_topology.ss2_3_subbasis

namespace Bourbaki

section Def

variable {X ι : Type _} {Y : ι → Type _}


def Init (_f : ∀ i, X → Y i) := X

def Init.to (f : ∀ i, X → Y i) (i : ι) : Init f → Y i := f i

@[simp]
lemma Init.to_apply (f : ∀ i, X → Y i) (i : ι) (x : Init f) :
  Init.to f i x = f i x := rfl

def Init_subbase [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :=
  {V | ∃ i U, U ∈ (HY i).isOpen ∧ V = Init.to f i ⁻¹' U}

lemma Init_subbase_isSubbase [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :
  let _Hf := GenedTopology (Init_subbase f)
  IsTopologicalSubbase (Init_subbase f)
:= by classical
  intro Hf x
  let G : @NeighborBase (Init f) Hf x Set.univ  := {
    base := {V | x ∈ V ∧ V ∈ {V | ∃ U : Finset (Set (Init f)), ↑U ⊆ Init_subbase f ∧ V = ⋂₀ ↑U}}
    base_isNeighbor := by
      intro S; simp
      intro Hx T HT rfl
      simp [neighborWithin]
      use ⋂₀ T
      use ?_, Hx, by grind
      apply isOpen_sInter (HX := Hf)
      intro t Ht
      apply HT at Ht
      simp [Init_subbase] at Ht
      change t ∈ Hf.isOpen
      rcases Ht with ⟨i, U, HU, rfl⟩
      apply GenedOpen.base
      simp [Init_subbase]
      use i, U
    cofinal := by
      intro S HS
      simp [neighborWithin] at HS
      rcases HS with ⟨U, HU, Ux, US⟩
      revert x Ux S US
      induction HU with
      | base U HU =>
        intro x S Hx US; simp
        use {U}; simp; grind
      | univ =>
        intro x S Hx HS
        simp at *; clear Hx
        subst S; simp
        use ∅; simp
      | inter S T HS HT IHS IHT =>
        intro x V ⟨Sx, Tx⟩ HV
        simp at IHS IHT
        specialize IHS x S Sx (by simp)
        specialize IHT x T Tx (by simp)
        rcases IHS with ⟨S', ⟨HS', HS''⟩, SS⟩
        rcases IHT with ⟨T', ⟨HT', HT''⟩, TT⟩
        simp
        use S' ∪ T'; grind
      | union V HV IHV =>
        intro x S Hx HS
        simp at Hx
        rcases Hx with ⟨v, Hv, xv⟩
        specialize IHV v Hv x (⋃₀ V) xv (by grind)
        rcases IHV with ⟨W, HW, WV⟩
        use W; grind
  }
  use G


instance Init.topology [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i) :
  Topology (Init f)
:= GenedTopology (Init_subbase f)

lemma Init.isOpen_iff [HY : ∀ i, Topology (Y i)] {f : ∀ i, X → Y i} U :
  U ∈ (Init.topology f).isOpen ↔ U ∈ {U | ∃ B ⊆ {V | ∃ U : Finset (Set (Init f)), ↑U ⊆ Init_subbase f ∧ V = ⋂₀ ↑U}, U = ⋃₀ B}
:= by
  conv => arg 1; change Topology.isOpen U
  rw [<- GenedTopology_eq (Init_subbase_isSubbase f)]; rfl


section Continuous

variable [HY : ∀ i, Topology (Y i)] (f : ∀ i, X → Y i)


lemma Init.to_continuous (i : ι) :
  IsContinuous (Init.to f i)
:= by
  rw [@IsContinuous_iff_IsOpen_preimage]
  intro U HU
  apply GenedOpen.base
  simp [Init_subbase]
  use i, U, HU


lemma le_Init [HX : Topology X] :
  (∀ i, IsContinuous (f i)) → HX ≤ Init.topology f
:= by
  intro Hf U HU
  induction HU with
  | base U HU =>
    simp [Init_subbase] at HU
    rcases HU with ⟨i, V, HV, rfl⟩
    specialize Hf i
    rw [@IsContinuous_iff_IsOpen_preimage] at Hf
    apply Hf V HV
  | univ => apply HX.isOpen_univ
  | inter S T HS HT IHS IHT => apply HX.isOpen_inter S T IHS IHT
  | union S HS IHS =>
    apply HX.isOpen_union
    intro s Hs
    apply IHS s Hs

lemma Init.IsContinuousAt_iff [HZ : Topology Z] (g : Z → Init f) (z : Z) :
  IsContinuousAt g z ↔ ∀ i, IsContinuousAt (Init.to f i ∘ g) z
:= by
  constructor<;> intro H
  · intro i U HU
    have Hf := to_continuous f i (g z) U HU
    have := H _ Hf
    simp [Init.to] at this ⊢
    rw [Set.preimage_comp]; assumption
  · intro U HU
    simp [neighborOf, NeighborOf] at HU ⊢
    rcases HU with ⟨V, HV, Vgz, VU⟩
    revert U
    induction HV with
    | base V HV =>
      intro U VU
      simp [Init_subbase] at HV
      rcases HV with ⟨i, W, HW, rfl⟩
      simp [Init.to] at *
      specialize H i W
      change (HY i).isOpen W at HW
      rw [<- mem_neighbor_iff_isOpen] at HW
      specialize HW  _ Vgz
      apply H at HW
      simp [neighborOf, NeighborOf] at HW
      rcases HW with ⟨A, HA, Az, AW⟩
      rw [Set.preimage_comp] at AW
      use A, HA, Az
      apply subset_trans AW
      apply Set.preimage_mono VU
    | univ =>
      intro U VU
      simp at *; subst U; simp
      use Set.univ; simp
      apply HZ.isOpen_univ
    | inter S T HS HT IHS IHT =>
      intro U VU
      rcases Vgz with ⟨Sz, Tz⟩
      specialize IHS Sz S (by simp)
      specialize IHT Tz T (by simp)
      rcases IHS with ⟨S', HS', HSz, SS⟩
      rcases IHT with ⟨T', HT', HTz, TT⟩
      have := HZ.isOpen_inter _ _ HS' HT'
      use S' ∩ T'; grind
    | union S HS IHS =>
      intro U VU
      simp at Vgz
      rcases Vgz with ⟨s, Hs, zs⟩
      have : s ⊆ ⋃₀ S := by grind
      specialize IHS s Hs zs (⋃₀ S) this
      rcases IHS with ⟨W, HW, Wz, WS⟩
      use W; grind


example (𝓑 : ∀ i, TopologicalBase (Y i)) :
   IsTopologicalSubbase {V : Set (Init f) | ∃ i U, U ∈ (𝓑 i).base ∧ V = Init.to f i ⁻¹' U}
:= by classical
  intro x; simp
  let G : NeighborBase x Set.univ := {
    base := {V | x ∈ V ∧ ∃ U : Finset (Set (Init f)), ↑U ⊆ {V | ∃ i, ∃ U ∈ (𝓑 i).base, V = Init.to f i ⁻¹' U} ∧ V = ⋂₀ ↑U}
    base_isNeighbor := by
      intro U HU; simp at HU
      rcases HU with ⟨Ux, V, HV, rfl⟩
      simp [neighborWithin]
      use ⋂₀ V, ?_, by grind, by grind
      apply isOpen_sInter
      intro v Hv; apply HV at Hv; simp at Hv
      rcases Hv with ⟨i, W, HW, rfl⟩
      apply GenedOpen.base
      simp [Init_subbase]; use i, W; simp
      apply (𝓑 i).base_isOpen HW
    cofinal := by
      intro V HV
      simp [neighborWithin] at HV
      rcases HV with ⟨U, HU, Ux, UV⟩
      revert x V
      induction HU with
      | base U HU =>
        intro x V Hx UV; simp
        simp [Init_subbase] at HU
        rcases HU with ⟨i, W, HW, rfl⟩
        have ⟨B, HB, E⟩ := (𝓑 i).covered _ HW
        subst W; simp at *
        rcases Hx with ⟨b, Bb, Hb⟩
        specialize UV b Bb
        use {Init.to f i ⁻¹' b}; simp
        grind
      | univ =>
        intro x V Hx UV; simp at *; subst V; simp
        use ∅; simp
      | inter S T HS HT IHS IHT =>
        intro x V ⟨Sx, Tx⟩ HV
        specialize IHS x S Sx (by simp)
        specialize IHT x T Tx (by simp)
        simp at IHS IHT
        rcases IHS with ⟨US, ⟨USx, HUS⟩, SS⟩
        rcases IHT with ⟨UT, ⟨UTx, HUT⟩, TT⟩
        use ⋂₀ US ∩ ⋂₀ UT
        constructor; swap
        · intro i ⟨H1, H2⟩
          apply HV; simp; grind
        · simp; constructor; grind
          rw [<- Set.sInter_union]
          use (US ∪ UT); simp; grind
      | union V HV IHV =>
        intro x S Hx HS
        simp at Hx
        rcases Hx with ⟨v, Hv, xv⟩
        specialize IHV v Hv x (⋃₀ V) xv (by grind)
        rcases IHV with ⟨W, HW, WV⟩
        use W, HW, by apply subset_trans WV HS
  }
  use G



end Continuous

end Def

lemma Init.trans {X I L : Type _} {Z : I →  Type _} {Y : L → Type _} [∀ ι, Topology (Z ι)]
   (h : ∀ l, X → Y l) (g : ∀ l, ∀ ι : I, Y l → Z ι) :
  let _HY : ∀ l, Topology (Y l) := λ l => Init.topology (fun ι => g l ι)
  Init.topology (fun p : L × I => g p.1 p.2 ∘ h p.1) = Init.topology h
:= by
  intro HY
  apply le_antisymm; swap
  · intro U HU
    induction HU with
    | base V HV =>
      simp [Init_subbase] at HV
      rcases HV with ⟨l, i, U, HU, rfl⟩
      apply GenedOpen.base
      simp [Init_subbase, Init.to, Set.preimage_comp]
      use l, g l i ⁻¹' U; simp
      have := Init.to_continuous (f := g l) i
      rw [@IsContinuous_iff_IsOpen_preimage] at this
      specialize this U HU
      exact this
    | univ =>
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      apply GenedOpen.inter S T IHS IHT
    | union S HS IHS =>
      apply GenedOpen.union S IHS
  · apply le_Init
    intro l
    rw [IsContinuous_iff_IsOpen_preimage]
    intro U HU
    induction HU with
    | base V HV =>
      simp [Init_subbase] at HV
      rcases HV with ⟨i, Hi, W, HW, rfl⟩
      apply GenedOpen.base
      simp [Init_subbase, Init.to, Set.preimage_comp]
      use l, i, Hi, W
    | univ =>
      apply GenedOpen.univ
    | inter S T HS HT IHS IHT =>
      simp
      apply GenedOpen.inter _ _ IHS IHT
    | union S HS IHS =>
      simp
      have : (⋃ t ∈ S, h l ⁻¹' t) = ⋃₀ { x | ∃ s ∈ S, x = h l ⁻¹' s } := by ext x; simp
      rw [this]; clear this
      apply GenedOpen.union
      intro x ⟨s, Hs, E⟩; rw [E]
      apply IHS s Hs

section inverse

def inverse {X : Type _}  {Y : Type _}  [HY : Topology Y] (f : X → Y) :
  Topology X
:= Init.topology (fun _ : PUnit.{1} => f)

def induced {X : Type} [Topology Y] (f : X ↪  Y) :
  Topology X
:= inverse (f : X → Y)

structure Subtopology (Y : Type _) [HY : Topology Y] where
  carrier : Type _
  inclusion : carrier ↪ Y

instance Subtopology.topology {Y : Type _} [HY : Topology Y] (S : Subtopology Y) :
  Topology S.carrier
:= induced S.inclusion


lemma IsContinuous_iff_le_inverse [HX : Topology X] [HX' : Topology X'] (f : X → X') :
  IsContinuous f ↔ HX ≤ inverse f
:= by
  constructor<;> intro H
  · simp [inverse]
    apply le_Init; simp
    assumption
  · simp [LE.le] at H
    rw [@IsContinuous_iff_IsOpen_preimage]
    intro U HU
    apply H
    apply GenedOpen.base
    simp [Init_subbase, Init.to]
    use U, HU

end inverse


def Init.inf {X I : Type _} (HX : I →  Topology X) :
  Topology X
:= Init.topology (HY := HX) (f := fun _ x => x)

lemma Init.le_inf {X I : Type _} (HX : I →  Topology X) :
  ∀ H, (∀ i, H ≤ HX i) → H ≤ inf HX
:= by
  intro H HH
  simp [inf]
  apply le_Init (HY := HX) (f := fun (_ : I) (x : X) => x)
  intro i
  specialize HH i; simp [LE.le] at HH
  rw [@IsContinuous_iff_IsOpen_preimage]
  intro U HU
  apply HH; simp; assumption



lemma Init.inf_le {X I : Type _} (HX : I →  Topology X) :
  ∀ i, inf HX ≤ HX i
:= by
  intro i U HU
  change U ∈ (inf HX).isOpen
  rw [Init.isOpen_iff (HY := HX) (f := fun (_ : I) (x : X) => x)]
  simp
  use {U}; simp
  use {U}; simp
  simp [Init_subbase, Init.to]
  use i, U, HU; rfl

end Bourbaki
