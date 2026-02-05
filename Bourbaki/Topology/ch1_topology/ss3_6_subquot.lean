import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace
import Bourbaki.Topology.ch1_topology.ss3_2_continuous
import Bourbaki.Topology.ch1_topology.ss3_3_locallyClosed
import Bourbaki.Topology.ch1_topology.ss3_4_quatient
import Bourbaki.Topology.ch1_topology.ss3_5_decompose

namespace Bourbaki

/-

  f : X → Y
  R : Setoid
  A : Set S
  に対して、
  g : A → X⧸R := Quotient.mk R ∘ Subtypev.val A
  とすると、gは連続なので標準分解がつくれる

  gとは、X → X⧸R のAへの制限であるから、Im g とは言うなれば  A⧸R である。
  decompose g : A → A⧸(R|A) → A⧸R → X⧸R

-/




def Subquot {X : Type _}  (R : Setoid X) (A : Set X) : Setoid A :=
  Setoid.comap (@Subtype.val X A) R

def Subquot.mk (R : Setoid X) (A : Set X) :
  A → Quotient R
:= Quotient.mk R ∘ @Subtype.val X A

lemma Subquot.mk_isContinuous [Topology X ] (A : Set X) (R : Setoid X) :
  IsContinuous (Subquot.mk R A)
:= by
  simp [Subquot.mk]
  apply IsContinuous_comp
  · apply Subtopology.isContinuous A
  · apply Quotspace.isContinuous


lemma Subquot.kerLift_IsContinuous [Topology X ] (A : Set X) (R : Setoid X) :
  IsContinuous (kerLift (Subquot.mk R A))
:= by
  apply kerLift_isContinuous
  apply Subquot.mk_isContinuous A R







lemma Subquot.kerLift_isHomeomorphic_iff_isOpen [HX : Topology X ] (A : Set X) (R : Setoid X) :
  IsHomeomorphic (kerLift (Subquot.mk R A)) ↔
  ∀ U ∈ (Subtopology A).isOpen, IsSaturated (Subquot.mk R A) U →
  ∃ V ∈ HX.isOpen, IsSaturated (Quotient.mk R) V ∧ U = {x : A | x.val ∈ V}
:= by
  constructor
  · intro H U HU HU'
    rw [kerLift_IsHomeomorphic_iff_isOpen (Subquot.mk R A) (Subquot.mk_isContinuous A R)] at H
    specialize H U HU HU'
    rw [Subtopology.isOpen_eq] at H
    rcases H with ⟨V, HV, E⟩
    rw [Quotspace.isOpen_iff] at HV
    use  Quotient.mk R ⁻¹' V, HV
    constructor
    ·
      intro x Hx y Exy; simp at Hx ⊢ Exy
      rw [<- Quotient.eq] at Exy
      rw [<- Exy]; exact Hx
    · ext x; simp
      have Hx : ⟦x.val⟧ ∈ Set.range (mk R A) := by simp; use x.val, x.prop; simp [mk]
      let x' : Set.range (mk R A) := ⟨⟦x.val⟧, Hx⟩
      constructor<;> intro H
      · have : x' ∈ {x : Set.range (mk R A)| ↑x ∈ mk R A '' U} := by
          simp [x', mk]; use x; simp; assumption
        rw [E] at this; simp [x'] at this
        exact this
      · have : x' ∈ {x : Set.range (mk R A)| ↑x ∈ V} := by simp [x']; grind
        rw [<- E] at this; simp [x'] at this
        rcases this with ⟨y, Ay, Uy, E⟩
        simp [mk] at E
        apply HU' ⟨y, Ay⟩ Uy x E
  · intro H; constructor
    · apply Subquot.kerLift_IsContinuous
    · constructor
      · intro x y
        simp [kerLift]
        rw [<- Quotient.out_eq x, <- Quotient.out_eq y, Quotient.liftOn_mk, Quotient.liftOn_mk]
        intro E; simp [mk] at E
        rw [Quotient.eq]; simp [mk]; rw [E]
      · intro ⟨x, Hx⟩; simp at Hx
        rcases Hx with ⟨a, Aa, E⟩
        simp [mk] at E
        use ⟦⟨a, Aa⟩⟧
        simp [kerLift, mk]; rw [E]
    · intro x U HU
      unfold neighborOf NeighborOf at HU; simp at HU
      rcases HU with ⟨V, HV, Vx, VU⟩
      change V ∈ Topology.isOpen at HV
      rw [Finale.isOpen_iff] at HV; simp at HV
      have : IsSaturated (mk R A) (Quotient.mk (Setoid.ker (mk R A)) ⁻¹' V) := by {
        intro a Ha b Hb; simp [mk] at Ha Hb ⊢
        have : (⟦b⟧ : Quotient (Setoid.ker (Quotient.mk R ∘ (@Subtype.val X A : Subtype A → X)) : Setoid A)) = ⟦a⟧ := by {
          rw [Quotient.eq, Setoid.ker_def]; simp; rw [Hb]
        }
        rw [this]; exact Ha
      }
      have := H (Quotient.mk (Setoid.ker (mk R A)) ⁻¹' V) HV this
      rcases this with ⟨W, HW, HW', E⟩
      clear this HV H
      rw [Subtopology.neighborOf_iff]
      use Quotient.mk R '' W
      constructor; swap
      · intro i Hi; simp at Hi ⊢
        rcases i with ⟨i, Hi'⟩; simp at Hi'
        rcases Hi' with ⟨a, Ha, Ea⟩; simp [mk] at Ea
        rcases Hi with ⟨w, Hw, Ew⟩; simp at Ew
        have E' := Ew.trans Ea.symm
        rw [Quotient.eq] at E'
        specialize HW' w Hw a; simp at HW'
        specialize HW' E'
        have : ⟨a, Ha⟩ ∈ {x : A | x.val ∈ W}:= by {
          simp; assumption
        }
        rw [<- E] at this; simp at this
        apply VU at this
        use ⟦⟨a, Ha⟩⟧, this
        simp [kerLift, mk]; rw [Ea]
      · unfold neighborOf NeighborOf; simp
        use Quotient.mk R '' W
        constructor; swap; constructor
        · simp [kerLift, mk]
          rw [<- Quotient.out_eq x, Quotient.liftOn_mk]
          have Hx : x.out ∈  Quotient.mk (Setoid.ker (mk R A)) ⁻¹' V := by simp; assumption
          rw [E] at Hx; simp at Hx
          use x.out, Hx
        · intro i Hi; simp at Hi ⊢
          exact Hi
        · change (Quotient.mk R '' W) ∈ Topology.isOpen
          rw [Finale.isOpen_iff]; simp
          have : W = Quotient.mk R ⁻¹' (Quotient.mk R '' W) := by {
            ext w; simp; constructor; grind
            intro ⟨w', Hw', Ew⟩
            rw [Quotient.eq] at Ew
            apply HW' w' Hw'; simp
            exact Ew
          }
          rw [<- this]; exact HW


lemma Subquot.kerLift_isHomeomorphic_iff_isClosed[HX : Topology X ] (A : Set X) (R : Setoid X) :
  IsHomeomorphic (kerLift (Subquot.mk R A)) ↔
  ∀ U, (Subtopology A).isClosed U → IsSaturated (Subquot.mk R A) U →
  ∃ V,  HX.isClosed V ∧ IsSaturated (Quotient.mk R) V ∧ U = {x : A | x.val ∈ V}
:= by
  rw [Subquot.kerLift_isHomeomorphic_iff_isOpen A R]
  constructor<;> intro H U HU HU'
  · specialize H Uᶜ HU ((IsSaturated_compl (mk R A) U).mp HU')
    rcases H with ⟨V, HV, HV', E⟩
    use Vᶜ; unfold Topology.isClosed; simp
    use HV, (IsSaturated_compl (Quotient.mk R) V).mp HV'
    rw [<- compl_compl U, E]; ext x; simp
  · rw [<- compl_compl U] at HU; change Topology.isClosed Uᶜ at HU
    specialize H Uᶜ HU ((IsSaturated_compl (mk R A) U).mp HU')
    rcases H with ⟨V, HV, HV', E⟩
    use Vᶜ, HV, (IsSaturated_compl (Quotient.mk R) V).mp HV'
    rw [<- compl_compl U, E]; ext x; simp


lemma Subquot.kerLift_isHomeomorphic [HX : Topology X ] (A : Set X) (R : Setoid X) :
  A ∈ HX.isOpen → IsSaturated (Quotient.mk R) A → IsHomeomorphic (kerLift (mk R A))
:= by
  intro HA H
  rw [kerLift_IsHomeomorphic_iff_isOpen (mk R A) (mk_isContinuous A R)]
  intro U HU HU'
  rw [Subtopology.isOpen_eq] at HU ⊢; simp at HU ⊢
  rcases HU with ⟨V, HV, rfl⟩; simp [mk] at ⊢
  use Quotient.mk R '' (V ∩ A)
  constructor; swap
  · ext x; simp
    rcases x with ⟨x, Hx⟩; simp at Hx; simp
    rcases Hx with ⟨a, Ha, rfl⟩
    simp at Hx ⊢
    rcases Hx with ⟨a', Ha', Ea'⟩
    constructor<;> intro Hx
    · rcases Hx with ⟨a'', Va'', Aa'', Ea''⟩
      grind
    · rcases Hx with ⟨a'', ⟨Va'', Aa''⟩, Ea''⟩
      use a''
  · rw [Finale.isOpen_iff]; simp
    have : (Quotient.mk R ⁻¹' (Quotient.mk R '' (V ∩ A)) )= V ∩ A := by {
      ext x; simp
      constructor<;> intro Hx
      · rcases Hx with ⟨y, ⟨Vy, Ay⟩, E⟩
        have Ax := H y Ay x E
        have := HU' ⟨y, Ay⟩ Vy ⟨x, Ax⟩ E; simp at this
        grind
      · rcases Hx with ⟨Vx, Ax⟩
        use x
    }
    rw [this]
    apply Topology.isOpen_inter _ _ HV HA


lemma Subquot.mk_surjective  [Topology X ] (R : Setoid X) (A : Set X) (u : X → A) (H : ∀ x, R x (u x).val) :
  (mk R A).Surjective
:= by
  intro x
  use (u x.out)
  simp [mk]
  specialize H x.out
  rw [<- Quotient.out_eq x, Quotient.eq]; simp
  exact R.symm H

lemma Subquot.isHomeomorphic' [Topology X ] (R : Setoid X) (A : Set X) (u : X → A) (Hu : IsContinuous u )(H : ∀ x, R x (u x).val) :
  IsHomeomorphic (kerLift (mk R A))
:= by
  rw [kerLift_isHomeomorphic_iff_isOpen]
  have Hmk := mk_surjective R A u H
  intro U HU HU'
  rw [IsContinuous_iff_IsOpen_preimage] at Hu
  have := Hu U HU
  use u ⁻¹' U, this
  constructor; swap
  · ext x; simp
    have Rx := H x
    rw [<- Quotient.eq] at Rx
    constructor<;> intro Hx
    · apply HU' x Hx (u x) (by simp [mk]; rw [Rx])
    · apply HU' (u x) Hx x (by simp [mk]; rw [Rx])
  · intro x Hx; simp at Hx
    intro y E; simp at E; simp
    apply HU' (u x) Hx (u y)
    simp [mk]
    rw [Quotient.eq]
    have Hx := (H x)
    have Hy := (H y)
    exact R.trans (R.trans (R.symm Hx) E) Hy
