import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace
import Bourbaki.Topology.ch1_topology.ss3_2_continuous
import Bourbaki.Topology.ch1_topology.ss3_3_locallyClosed

namespace Bourbaki

def Quotspace [HX : Topology X] (R : Setoid X) :
  Topology (Quotient R)
:= Finale.quotient R

lemma Quotspace.isOpen_iff [HX : Topology X] (R : Setoid X) (U : Set (Quotient R)) :
  U ∈ (Quotspace R).isOpen ↔  (Quotient.mk R ⁻¹' U) ∈ Topology.isOpen
:= by rw [Finale.isOpen_iff]; simp; conv => arg 1; change Quotient.mk R ⁻¹' U ∈ Topology.isOpen



lemma Quotspace.isOpen_iff'  [HX : Topology X] (R : Setoid X) (U : Set (Quotient R)) :
  U ∈ (Quotspace R).isOpen ↔ ∃ V ∈ HX.isOpen, V =  Quotient.mk R ⁻¹' U ∧ U = Quotient.mk R '' V
:= by
  rw [isOpen_iff]
  constructor<;> intro H
  · use Quotient.mk R ⁻¹' U, H; simp
    ext x; simp
    rw [<- Quotient.out_eq x]
    constructor<;> intro Hx; grind
    rcases Hx with ⟨y, Hy, E⟩; grind
  · rcases H with ⟨V, HV, EV, EU⟩
    rw [<- EV]; assumption

lemma Quotspace.isContinuous_iff [HX : Topology X] [HY : Topology Y] (R : Setoid X) (f : Quotient R → Y) :
  IsContinuous f ↔ IsContinuous (f ∘ Quotient.mk R)
:= by
  have E := Finale.isContinuous_iff (g := f) (f := fun ( _ : PUnit.{1}) => Quotient.mk R)
  simp at E
  conv at E => arg 1; change @IsContinuous (Quotient R) Y (Finale.quotient R) HY f
  rw [E]



def Quotspace.map [HX : Topology X] [HY : Topology Y] {R : Setoid X} {S : Setoid Y} {f : X → Y} (Hf : R ≤ Setoid.comap f S) :
  Quotient R → Quotient S
:= fun x => by
  apply Quotient.liftOn x (Quotient.mk S ∘ f)
  intro x y H; simp
  apply Quotient.sound
  apply Hf H



lemma Quotspace.isContinuous [Topology X] [Topology Y] (R : Setoid X)  (S : Setoid Y) (f : X → Y) (Hf : R ≤ Setoid.comap f S) :
  IsContinuous f → IsContinuous (map Hf)
:= by
  intro H
  rw [isContinuous_iff]
  rw [IsContinuous_iff_IsOpen_preimage] at H ⊢
  intro U HU
  change U ∈ Topology.isOpen at HU
  rw [Quotspace.isOpen_iff] at HU
  apply H at HU
  have : (f ⁻¹' (Quotient.mk S ⁻¹' U)) = (map Hf ∘ Quotient.mk R ⁻¹' U) := by {
    ext x; simp [map]
  }
  rw [this] at HU
  exact HU

def Setoid.quontRel {X : Type _} {R S : Setoid X} (H : R ≤ S) :
  Setoid (Quotient R)
where
  r x y := by
    apply Quotient.liftOn₂ x y (fun a b => S a b)
    intro a₁ a₂ b₁ b₂ H₁ H₂
    apply H at H₁; apply H at H₂
    apply Quotient.sound (s := S) at H₁
    apply Quotient.sound (s := S) at H₂
    ext
    constructor<;> intro HS<;>
     apply Quotient.sound (s := S) at HS<;>
     apply Quotient.exact<;> grind
  iseqv := {
    refl x := by
      rw [<- Quotient.out_eq x]
      rw [Quotient.liftOn₂_mk]
    symm {x y} := by
      rw [<- Quotient.out_eq x, <- Quotient.out_eq y]
      rw [Quotient.liftOn₂_mk, Quotient.liftOn₂_mk]
      intro H; apply S.symm H
    trans {x y z} := by
      rw [<- Quotient.out_eq x, <- Quotient.out_eq y, <- Quotient.out_eq z]
      rw [Quotient.liftOn₂_mk, Quotient.liftOn₂_mk, Quotient.liftOn₂_mk]
      intro Hxy Hy
      apply S.trans Hxy Hy
  }


def Quotspace.trans {X : Type _} {R S : Setoid X} (RS : R ≤ S) :
  -- (X⧸R) ⧸ (R⧸S) → X ⧸ S
  Quotient (Setoid.quontRel RS) → Quotient S
:= fun x => by
  apply Quotient.liftOn x (fun s => Quotient.liftOn s (Quotient.mk S) ?H ) ?Hf; swap
  · intro a b Hab
    rw [Quotient.eq]; apply RS Hab
  · intro a b E; simp
    unfold HasEquiv.Equiv instHasEquivOfSetoid Setoid.quontRel at E; simp at E
    rw [<- Quotient.out_eq a, <- Quotient.out_eq b] at E ⊢
    rw [Quotient.liftOn₂_mk] at E
    rw [Quotient.liftOn_mk, Quotient.liftOn_mk, Quotient.eq]
    exact E


lemma Quotspace.isTopologyHom [HX : Topology X] (R S : Setoid X) (RS : R ≤ S) :
  -- (X⧸R) ⧸ (R⧸S) ≅ X ⧸ S
  IsTopologyHom (trans RS)
where
  continuous := by
    rw [isContinuous_iff, IsContinuous_iff_IsOpen_preimage]
    intro U (HU : U ∈ Topology.isOpen)
    change (trans RS ∘ Quotient.mk (Setoid.quontRel RS) ⁻¹' U) ∈ Topology.isOpen
    rw [Quotspace.isOpen_iff] at HU ⊢
    have : Quotient.mk R ⁻¹' (trans RS ∘ Quotient.mk (Setoid.quontRel RS) ⁻¹' U) = Quotient.mk S ⁻¹' U := by {
      ext x; simp [trans]
    }
    rw [this]; exact HU
  bij := by
    constructor
    · intro x y Hxy; simp [trans] at Hxy
      rw [<- Quotient.out_eq x, <- Quotient.out_eq y] at Hxy ⊢
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk] at Hxy
      rw [Quotient.eq]; simp [Setoid.quontRel]
      rw [<- Quotient.out_eq x.out, <- Quotient.out_eq y.out] at ⊢ Hxy
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk, Quotient.eq] at Hxy
      rw [Quotient.liftOn₂_mk]
      exact Hxy
    · intro x; simp [trans]
      use ⟦⟦x.out⟧⟧
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk, Quotient.out_eq]
  open_map := by
    intro x U HU
    unfold neighborOf NeighborOf at HU ⊢; simp at HU ⊢
    rcases HU with ⟨V, HV, Vx, VU⟩
    change V ∈ Topology.isOpen at HV
    rw [isOpen_iff, isOpen_iff] at HV
    use Quotient.mk S '' (Quotient.mk R ⁻¹' (Quotient.mk (Setoid.quontRel RS) ⁻¹' V))
    constructor
    · change ((Quotient.mk S '' (Quotient.mk R ⁻¹' (Quotient.mk (Setoid.quontRel RS) ⁻¹' V)))) ∈ Topology.isOpen
      rw [isOpen_iff]
      have : Quotient.mk S ⁻¹' (Quotient.mk S '' (Quotient.mk R ⁻¹' (Quotient.mk (Setoid.quontRel RS) ⁻¹' V))) =  Quotient.mk R ⁻¹' (Quotient.mk (Setoid.quontRel RS) ⁻¹' V) := by {
        ext a; simp
        constructor<;> try grind
        intro ⟨b, Hb, E⟩
        have : (⟦⟦a⟧⟧ : Quotient (Setoid.quontRel RS)) = ⟦⟦b⟧⟧ := by {
          rw [Quotient.eq] at ⊢ E; simp [Setoid.quontRel]
          apply S.symm E
        }
        rw [this]; exact Hb
      }
      rw [this]; exact HV
    constructor
    · simp [trans]
      rw [<- Quotient.out_eq x, <- Quotient.out_eq x.out] at Vx ⊢
      use x.out.out, Vx
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk]
    · intro x Hx; simp [trans] at *
      rcases Hx with ⟨y, Hy, E⟩
      use ⟦⟦y⟧⟧; constructor; apply VU Hy
      rw [Quotient.liftOn_mk, Quotient.liftOn_mk, E]
