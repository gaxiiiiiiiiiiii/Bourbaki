import Mathlib.tactic

namespace Bourbaki


-- 位相空間
class Topology (X : Type _) where
  isOpen : Set X → Prop
  isOpen_inter (s t : Set X ): isOpen s → isOpen t → isOpen (s ∩ t)
  isOpen_union (S : Set (Set X)) : (∀ s ∈ S, isOpen s) → isOpen (⋃₀ S)
  isOpen_univ : isOpen (Set.univ : Set X)

lemma Topology.isOpen_empty [Topology X] : isOpen (∅ : Set X)
:= by
  have := isOpen_union (∅ : Set (Set X)); simp at this
  exact this


-- 被覆
@[ext]
structure Cover (X : Type _) where
  carrier : Set (Set X)
  isCover : (⋃₀ carrier) = Set.univ

instance : SetLike (Cover X) (Set X) where
  coe c := c.carrier
  coe_injective' := by
    intro x y; simp; intro H
    ext i; rw [H]

-- 開被覆
structure OpenCover (X : Type _) [Topology X] extends Cover X where
  open_in_cover : ∀ s ∈ carrier, Topology.isOpen s


-- 位相同型
structure TopologyHom (X Y : Type _) [Topology X] [Topology Y] extends X ≃ Y where
  continuous_fun : ∀ S : Set Y, Topology.isOpen S → Topology.isOpen (toFun ⁻¹' S)
  continuous_inv : ∀ S : Set X, Topology.isOpen S → Topology.isOpen (invFun ⁻¹' S)


-- 近傍
def NeighborOf [HX : Topology X] (A : Set X) :=
  {V : Set X | ∃ U, HX.isOpen U ∧ A ⊆ U ∧ U ⊆ V}

def neighborOf [HX : Topology X] (x : X) :=
  NeighborOf {x}
  -- {V | ∃ U, isOpen U ∧ x ∈ U ∧ U ⊆ V}

def neighborWithin [HX : Topology X] (x : X) (A : Set X) :=
  {V : Set X | ∃ U, HX.isOpen U ∧ x ∈ U ∧ U ∩ A ⊆ V}

lemma neighborWithin_neighborOf [HX : Topology X] (x : X) :
  neighborWithin x Set.univ = neighborOf x
:= by
  ext U; simp [neighborWithin, neighborOf, NeighborOf]


-- 近傍系の特徴付け
lemma neighborOf_notempty [HX : Topology X] (x : X) :
  (neighborOf x).Nonempty
:= by
  use Set.univ; simp [neighborOf, NeighborOf]
  use Set.univ; simp
  apply HX.isOpen_univ


lemma neighbor_mem_iff_isOpen [HX : Topology X]  {V : Set X} :
    (∀ x ∈ V, V ∈ neighborOf x) ↔  HX.isOpen V
  := by
    simp [neighborOf, NeighborOf]
    constructor<;> intro H
    · let S := {U | HX.isOpen U ∧ U ⊆ V}
      have E : ⋃₀ S = V := by {
        ext x; simp [S]
        constructor<;> intro Hx
        · rcases Hx with ⟨U, ⟨HU, UV⟩, Ux⟩
          apply UV Ux
        · have ⟨U, HU, Ux, UV⟩ := H x Hx
          use U
      }
      rw [<- E]
      apply HX.isOpen_union S
      intro s; simp [S]; grind
    · intro v Hv; use V

lemma neighborOf_subset [HX : Topology X] {x : X} {V W : Set X} :
    V ∈ neighborOf x → V ⊆ W → W ∈ neighborOf x
:= by
  intro HV VW
  simp [neighborOf, NeighborOf] at ⊢ HV
  rcases HV with ⟨U, HU, Ux, UW⟩
  use U, HU, Ux; grind

lemma neighborOf_inter [HX : Topology X] {x : X} {V W : Set X} :
  V ∈ neighborOf x → W ∈ neighborOf x → (V ∩ W) ∈ neighborOf x
:= by
  intro HV HW
  simp [neighborOf, NeighborOf] at ⊢ HV HW
  rcases HV with ⟨V', HV', xV', VV⟩
  rcases HW with ⟨W', HW', xW', WW⟩
  use (V' ∩ W'), HX.isOpen_inter V' W' HV' HW', ⟨xV', xW'⟩
  grind


lemma neighborOf_sInter [HX : Topology X] {x : X} {S : Finset (Set X)} :
  (∀ V ∈ S, V ∈ neighborOf x) → (⋂₀ S) ∈ neighborOf x
:= by
  induction S using Finset.cons_induction with
  | empty =>
    simp [neighborOf, NeighborOf]
    use Set.univ; simp
    apply HX.isOpen_univ
  | cons A T F IH =>
    simp; intro HA H
    apply neighborOf_inter HA
    apply IH H




lemma neighborOf_mem_self [HX : Topology X] {x : X} {V : Set X} :
  V ∈ neighborOf x → x ∈ V
:= by
  simp [neighborOf, NeighborOf]; grind


lemma neighbor_core {X} [HX : Topology X] {x : X} {V : Set X} :
  V ∈ neighborOf x → ∃ W ∈ neighborOf x, ∀ y ∈ W, V ∈ neighborOf y
:= by
  intro ⟨U, HU, Ux, UV⟩
  simp at Ux
  rw [<- neighbor_mem_iff_isOpen] at HU
  have Hx := HU x Ux
  use U, Hx
  intro y Uy
  have Hy := HU y Uy
  apply neighborOf_subset Hy UV


-- 近傍の公理
structure NeighborClass (X : Type _) where
  neighbor : X → Set (Set X)
  nonempty : ∀ x, (neighbor x).Nonempty
  subset : ∀ x (V W : Set X), V ∈ neighbor x → V ⊆ W → W ∈ neighbor x
  inter : ∀ x (V W : Set X), V ∈ neighbor x → W ∈ neighbor x → (V ∩ W) ∈ neighbor x
  mem_self : ∀ x (V : Set X), V ∈ neighbor x → x ∈ V
  core : ∀ x (V : Set X), V ∈ neighbor x → ∃ W ∈ neighbor x, ∀ y ∈ W, V ∈ neighbor y


instance NeighborClass.topology {X : Type _} (N : NeighborClass X)
  : Topology X
where
  isOpen A  := ∀ x ∈ A, A ∈ N.neighbor x
  isOpen_inter S T HS HT x Hx := by
    rcases Hx with ⟨Sx, Tx⟩
    apply N.inter x S T (HS x Sx) (HT x Tx)
  isOpen_union 𝓑 H x Hx := by
    rcases Hx with ⟨S, HS, Sx⟩
    have := H S HS x Sx
    apply N.subset x S _ this
    intro y Hy; simp
    use S
  isOpen_univ := by
    simp; intro x
    have ⟨V, HV⟩ := N.nonempty x
    apply N.subset x V _ HV; simp

lemma NeighborClass.neighbor_eq_neighborOf {X : Type _} (N : NeighborClass X) :
    ∀ x, N.neighbor x = neighborOf (HX := N.topology) x
:= by
  intro x
  ext S; simp [neighborOf, NeighborOf]
  unfold Topology.isOpen NeighborClass.topology; simp
  constructor<;> intro H; swap
  · rcases H with ⟨U, HU, Ux, US⟩
    apply N.subset x U S (HU x Ux) US
  ·
    let U : Set X := {y | ∃ V, V ∈ N.neighbor y ∧ V ⊆ S}
    use U; constructor
    · intro y Hy; simp [U] at Hy
      rcases Hy with ⟨V, HV, VS⟩
      have ⟨W, HW, HW'⟩:= N.core y V HV
      apply N.subset y W _ HW
      intro i Hi; simp [U]
      specialize HW' i Hi
      use V, HW', VS
    constructor
    · simp [U]; use S
    · intro y ⟨V, HV, VS⟩
      apply VS
      apply N.mem_self y V HV


-- 近傍系
structure NeighborBase [Topology X] (x : X) (A : Set X) where
  base : Set (Set X)
  base_isNeighbor : base ⊆ neighborWithin x A
  cofinal : ∀ V ∈ neighborWithin x A, ∃ W ∈ base, W ⊆ V

-- 基底
structure TopologicalBase (X : Type _) [HX : Topology X] where
  base : Set (Set X)
  base_isOpen : base ⊆ HX.isOpen
  covered : ∀ U, HX.isOpen U → ∃ B ⊆ base, U = ⋃₀ B

def IsTopologicalBase [HX : Topology X] (B : Set (Set X)) :=
  ∀ x, ∃ G : NeighborBase x Set.univ, G.base = {V | x ∈ V ∧ V ∈ B}

lemma TopologicalBase.isTopologicalBase [HX : Topology X] (B : TopologicalBase X) :
  IsTopologicalBase B.base
:= by
  intro x
  let G : NeighborBase x Set.univ :=
    { base := {V | x ∈ V ∧ V ∈ B.base}
      base_isNeighbor := by
        intro V HV; simp at HV; rcases HV with ⟨Vx, VB⟩
        simp [neighborWithin]
        apply B.base_isOpen at VB
        use V, VB, Vx
      cofinal := by
        intro V HV
        simp [neighborWithin] at HV
        rcases HV with ⟨U, HU, Ux, UV⟩
        have ⟨W, WB, E⟩:= B.covered U HU
        subst U; simp at Ux
        rcases Ux with ⟨U, UW, Ux⟩
        specialize WB UW
        have := B.base_isOpen WB
        use U; simp
        use ⟨Ux, WB⟩
        intro y Hy; apply UV; simp
        use U
    }
  use G

def IsTopologicalBase.topologicalBase [HX : Topology X] {B : Set (Set X)} (H : IsTopologicalBase B) :
  TopologicalBase X
where
  base := B
  base_isOpen := by
    intro S HS
    change HX.isOpen S
    rw [<- neighbor_mem_iff_isOpen]
    intro x Hx; simp [neighborOf, NeighborOf]
    have ⟨G, E⟩ := H x
    have SG : S ∈ G.base := by rw [E]; grind
    have ⟨W, HW, Wx, WS⟩ := G.base_isNeighbor SG; simp at WS
    use W
  covered := by
    intro U HU
    use {V | V ∈ B ∧ V ⊆ U}
    constructor
    · intro V; simp; grind
    · ext x; simp
      have ⟨G, E⟩ := H x
      have HG1 := G.base_isNeighbor
      have HG2 := G.cofinal
      constructor<;> intro Hx
      · have HU : U ∈ neighborWithin x Set.univ := by {
          simp [neighborWithin]
          use U, HU, Hx
        }
        have ⟨W, WB, UW⟩ := G.cofinal U HU
        rw [E] at WB
        simp at WB; rcases WB with ⟨Wx, WB⟩
        use W
      · rcases Hx with ⟨W, ⟨WB, WU⟩, Wx⟩
        grind



-- 閉集合
def Topology.isClosed [HX : Topology X] (A : Set X) := HX.isOpen Aᶜ

lemma isClosed_inter [HX : Topology X] (S : Set (Set X)) :
  (∀ s ∈ S, HX.isClosed s) → HX.isClosed (⋂₀ S)
:= by
  intro H; simp [Topology.isClosed]
  rw [@Set.compl_sInter]
  apply HX.isOpen_union
  intro s Hs; simp at Hs
  rcases Hs with ⟨s', Hs', E⟩
  subst s
  apply H s' Hs'

lemma isClosed_union [HX : Topology X] (s t : Set X) :
  HX.isClosed s → HX.isClosed t → HX.isClosed (s ∪ t)
:= by
  intro Hs Ht; simp [Topology.isClosed]
  apply HX.isOpen_inter<;> assumption

structure ClosedCover (X : Type _) [HX : Topology X] extends Cover X where
  closed_in_cover : ∀ s ∈ carrier, HX.isClosed s


-- 局所有限族
def LocallyFinite [Topology X] {ι : Type _} (f : ι → Set X) :=
  ∀ x : X, ∃ t ∈ neighborOf x, {i : ι | (f i ∩ t).Nonempty}.Finite

lemma LocallyFinte.subset [Topology X] {ι : Type _} {f g : ι → Set X}
    (Hf : LocallyFinite f) (Hg : ∀ i, g i ⊆ f i) :
    LocallyFinite g
:= by
  intro x
  have ⟨t, Ht, E⟩ := Hf x
  use t, Ht
  apply E.subset
  intro i; simp
  intro ⟨x, Hgx, Htx⟩
  apply Hg at Hgx
  use x; grind

lemma union_of_ClosedLocallyFinite_isClosed [HX : Topology X] {ι : Type _}  (f : ι → Set X)
  (Hf : LocallyFinite f) (Hf' : ∀ i, HX.isClosed (f i)) :
  HX.isClosed (⋃ i, f i)
:= by
  simp [Topology.isClosed]
  rw [<- neighbor_mem_iff_isOpen]
  intro x Hx; simp at Hx
  have ⟨t, Ht, E⟩ := Hf x
  let F := E.toFinset
  let W := t ∩ ⋂ i ∈ F, (f i)ᶜ
  apply neighborOf_subset (V := W); swap
  · simp [W]
    intro i y ⟨Hy1, Hy2⟩ Fy; simp [F] at Hy2
    apply Hy2 i ?_ Fy
    use y; grind
  · simp [W]
    rcases (F : Set ι).eq_empty_or_nonempty with HF | HF
    · simp at HF; rw [HF]; simp; assumption
    · have := Set.inter_biInter HF (λ i => (f i)ᶜ) t; simp at this
      rw [<- this]
      induction F using Finset.cons_induction with
      | empty =>
        simp [neighborOf, NeighborOf]
        use Set.univ; simp
        apply HX.isOpen_univ
      | cons j S Fi IH =>
        simp
        apply neighborOf_inter ?_ IH
        specialize Hf' j; rw [Topology.isClosed, <- neighbor_mem_iff_isOpen] at Hf'; simp at Hf'
        apply neighborOf_inter Ht
        apply Hf'
        apply Hx


-- 内点

def interior [HX : Topology X] (A : Set X) :=
  ⋃₀ {U | HX.isOpen U ∧ U ⊆ A}

lemma interior_isOpen [HX : Topology X] (A : Set X) :
  HX.isOpen (interior A)
:= by
  simp [interior]
  apply HX.isOpen_union; simp; grind

lemma interior_le [HX : Topology X] (A : Set X) :
  ∀ U ⊆ A, HX.isOpen U → U ⊆ interior A
:= by
  intro U AU HU x Hx
  simp [interior]
  use U

lemma mem_interior_iff_neighborOf [HX : Topology X] {A : Set X} {x : X} :
  x ∈ interior A ↔ A ∈ neighborOf x
:= by
  simp [interior, neighborOf, NeighborOf]; grind

lemma interior_mono [HX : Topology X] {A B : Set X} :
  A ⊆ B → interior A ⊆ interior B
:= by
  intro H x Hx; simp [interior] at Hx ⊢
  rcases Hx with ⟨U, ⟨HU, UA⟩, Ux⟩
  use U, ⟨HU, by grind⟩, Ux

lemma NeighborOf_iff_subset_interior [HX : Topology X] {A B : Set X} :
  A ∈ NeighborOf B ↔ B ⊆ interior A
:= by
  simp [NeighborOf, interior]
  constructor<;> intro H
  · intro x Hx; simp
    grind
  · use interior A; constructor; apply interior_isOpen
    constructor
    · intro x Hx; simp [interior]
      specialize H Hx; simp at H
      exact H
    · intro x Hx; simp [interior] at Hx
      rcases Hx with ⟨U, ⟨HU, UA⟩, Ux⟩
      grind
lemma isOpen_iff_eq_interior [HX : Topology X] {A : Set X} :
  HX.isOpen A ↔ interior A = A
:= by
  constructor<;> intro H
  · ext x; simp [interior]
    constructor<;> intro Hx
    · grind
    · use A
  · rw [<- H]; apply interior_isOpen

lemma interior_inter [HX : Topology X] (A B : Set X) :
  interior (A ∩ B) = interior A ∩ interior B
:= by
  ext x; simp [interior]
  constructor<;> intro Hx
  · rcases Hx with ⟨U, ⟨HU, UA, UB⟩, Ux⟩
    constructor<;> use U
  · rcases Hx with ⟨HA, HB⟩
    rcases HA with ⟨UA, ⟨HUA, HAA⟩, UAx⟩
    rcases HB with ⟨UB, ⟨HUB, HBA⟩, UBx⟩
    use (UA ∩ UB)
    constructor; constructor
    · apply HX.isOpen_inter _ _ HUA HUB
    constructor
    · intro x ⟨Hx, _⟩; apply HAA Hx
    · intro x ⟨_, Hx⟩; apply HBA Hx
    · simp; grind


-- 外部
def exterior [HX : Topology X] (A : Set X) :=
  ⋃₀ (compl '' {U | HX.isClosed U ∧ A ⊆ U})

lemma interior_compl_eq_exterior  [HX : Topology A] (S : Set A) :
  interior Sᶜ = exterior S
:= by
  ext x
  simp [exterior, interior, Topology.isClosed]
  constructor<;> intro ⟨T, ⟨HT, TS⟩, Tx⟩<;> use Tᶜ<;> simp<;> grind

lemma exterior_compl_eq_interior [HX : Topology A] (S : Set A) :
  exterior Sᶜ = interior S
:= by
  rw [<- interior_compl_eq_exterior, compl_compl]

lemma mem_exterior_iff [HX : Topology X] {A : Set X} {x : X} :
  x ∈ exterior A ↔ ∃ U ∈ neighborOf x, U ∩ A = ∅
:= by
  simp [exterior, neighborOf, NeighborOf]
  constructor<;> intro H
  · rcases H with ⟨U, ⟨HU, AU⟩, Ux⟩
    use Uᶜ; constructor
    · use Uᶜ; simp
      simp [Topology.isClosed] at HU; grind
    · ext x; simp
      intro Fx Hx; apply Fx; grind
  · rcases H with ⟨U, ⟨V, HV, Vx, VU⟩, E⟩
    use Vᶜ; simp [Topology.isClosed]
    use ⟨HV, ?_⟩, Vx
    intro y Hy Fy
    apply VU at Fy
    have : y ∈ U ∩ A := by grind
    rw [E] at this; contradiction

lemma mem_interior_iff [HX : Topology X] {A : Set X} {x : X} :
  x ∈ interior A ↔ ∃ U ∈ neighborOf x, U ∩ Aᶜ = ∅
:= by
  rw [<- exterior_compl_eq_interior, mem_exterior_iff]



-- 閉包
def closure [HX : Topology X] (A : Set X) :=
  ⋂₀ {F | HX.isClosed F ∧ A ⊆ F}

lemma closure_isClosed [HX : Topology X] (A : Set X) :
  HX.isClosed (closure A)
:= by
  simp [closure]
  apply isClosed_inter; grind


def closure_mem_iff_adherent [HX : Topology X] {A : Set X} {x : X} :
  x ∈ closure A ↔ ∀ B, B ∈ neighborOf x → A ∩ B ≠ ∅
:= by
  constructor<;> intro H
  · intro B HB F
    simp [closure] at H
    simp [neighborOf, NeighborOf] at HB
    rcases HB with ⟨U, HU, Ux, UB⟩
    rw [<- compl_compl U] at HU
    change HX.isClosed Uᶜ at HU
    apply H Uᶜ HU ?_ Ux
    intro y Ay Uy
    apply UB at Uy
    have : y ∈ A ∩ B := by grind
    rw [F] at this; contradiction
  · simp [closure]
    intro C HC AC
    by_contra F
    rw [Topology.isClosed, <- neighbor_mem_iff_isOpen] at HC
    apply HC at F
    apply H at F
    apply F
    ext x; simp; grind

lemma comple_closure_eq_interior_compl [HX : Topology X] (A : Set X) :
  (closure A)ᶜ = interior Aᶜ
:= by
  simp [closure, interior]
  rw [Set.compl_sInter]
  ext x; simp [Topology.isClosed]
  constructor<;> intro ⟨B, ⟨HB, AB⟩, Bx⟩<;> use Bᶜ<;> simp<;> grind

lemma compl_interior_eq_closure_compl [HX : Topology X] (A : Set X) :
  (interior A)ᶜ = closure Aᶜ
:= by
  conv => arg 1; rw [<- compl_compl A, <- comple_closure_eq_interior_compl, compl_compl]

lemma closure_le [HX : Topology X] (A : Set X) :
  ∀ B, HX.isClosed B → A ⊆ B → closure A ⊆ B
:= by
  intro B HB AB x Hx
  simp [closure] at Hx
  grind

lemma isCloses_iff_eq_closure [HX : Topology X] {A : Set X} :
  HX.isClosed A ↔ closure A = A
:= by
  simp [Topology.isClosed]
  rw [isOpen_iff_eq_interior]
  constructor<;> intro H
  · conv => arg 2; rw [<- compl_compl A, <- H]
    conv => arg 1; rw [<- compl_compl A, <- compl_interior_eq_closure_compl]
  · conv => arg 2; rw [<- H, comple_closure_eq_interior_compl]

lemma closure_union [HX : Topology X] (A B : Set X) :
  closure (A ∪ B) = closure A ∪ closure B
:= by
  ext x; simp [closure]
  constructor<;> intro H
  · by_contra F; simp at F; rcases F with ⟨FA, FB⟩
    rcases FA with ⟨A', HA', AA, Ax⟩
    rcases FB with ⟨B', HB', BB, Bx⟩
    have HAB := isClosed_union A' B' HA' HB'
    have := H _ HAB (by grind) (by grind)
    revert this; simp; grind
  · intro C HC AC BC; by_contra F
    revert H; simp
    constructor<;> use C

lemma inter_closure_le_closure_inter [HX : Topology X] (A B : Set X) (HA : HX.isOpen A) :
   A ∩ closure B ⊆ closure (A ∩ B)
:= by
  intro x; simp [closure]
  intro Hx H C HC ABC
  have HA' : HX.isClosed Aᶜ := by simp [Topology.isClosed]; assumption
  have HAC := isClosed_union _ _ HA' HC
  have BAC : B ⊆ Aᶜ ∪ C := by {
    intro x Bx; simp
    rw [@or_iff_not_imp_left]; simp
    intro Ax
    apply ABC; grind
  }
  have := H _ HAC BAC
  rcases this; contradiction; assumption

lemma closure_mono [HX : Topology X] {A B : Set X} :
  A ⊆ B → closure A ⊆ closure B
:= by
  intro H x
  rw [closure_mem_iff_adherent, closure_mem_iff_adherent]
  intro Hx U HU F
  specialize Hx U HU
  apply Hx; ext y; simp
  intro Ay Fy
  specialize H Ay
  have : y ∈ B ∩ U := by grind
  grind


example [HX : Topology X] (A : Set X) :
  ∀ x ∈ closure A, x ∉ A → ∀ B ∈ neighborOf x, ∃ y ∈ A, y ∈ B ∧ x ≠ y
:= by
  intro x Hx Fx B HB
  simp [closure_mem_iff_adherent] at Hx
  specialize Hx B HB
  by_contra F; simp at F
  apply Hx; ext y; simp
  intro Ay By
  specialize F y Ay By
  subst y
  contradiction

def isolate [HX : Topology X] (A : Set X) :=
  {x ∈ A | x ∉ closure (A \ {x})}


lemma isolate_mem_neighbor [HX : Topology X] {A : Set X} {x : X} :
  x ∈ isolate A → ∃ B ∈ neighborOf x, ∀ y ∈ B ∩ A, y = x
:= by
  simp [isolate]
  rw [closure_mem_iff_adherent]
  intro Ax H; simp at H
  rcases H with ⟨B, HB, EB⟩
  use B, HB
  intro y By Ay
  by_contra F
  have : y ∈ A \ {x} ∩ B := by simp; grind
  rw [EB] at this; contradiction

def frontier [HX : Topology X] (A : Set X) :=
  closure A ∩ closure Aᶜ

lemma frontier_isCloses [HX : Topology X] (A : Set X) :
  HX.isClosed (frontier A)
:= by
  simp [frontier]
  rw [<- Set.sInter_pair]
  apply isClosed_inter
  intro x Hx
  rcases Hx<;> subst x<;> apply closure_isClosed

lemma frontie_mem_iff [HX : Topology X] {A : Set X} {x : X} :
  x ∈ frontier A ↔
  (∀ B, B ∈ neighborOf x → A ∩ B ≠ ∅ ∧ Aᶜ ∩ B ≠ ∅)
:= by
  simp [frontier]
  rw [closure_mem_iff_adherent, closure_mem_iff_adherent]
  grind

lemma frontier_compl_eq [HX : Topology X] (A : Set X) :
  frontier A = frontier Aᶜ
:= by
  simp [frontier]; grind


-- 密
def Dense [HX : Topology X] (A : Set X) :=
  ∀ x, x ∈ closure A

end Bourbaki
