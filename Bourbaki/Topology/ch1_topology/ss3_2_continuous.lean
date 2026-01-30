import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace

namespace Bourbaki

def Subtopology.incl [Topology X] (A : Set X) : A → X := Subtype.val

def Subtopology.incl_isContinuous [HX : Topology X] (A : Set X) :
  IsContinuous (incl A )
:= Init.isContinuous (fun _ : PUnit.{1} => (Function.Embedding.subtype A).1) PUnit.unit

def Subtopology.restrict [HX : Topology X] (f : X → Y) (A : Set X) : A → Y := f ∘ incl A

lemma Subtopology.restrict_isContinuous [HX : Topology X] [HY : Topology Y]
  {A : Set X} {f : X → Y} (Hf : IsContinuous f) :
  @IsContinuous A Y (Subtopology A) HY (restrict f A)
:= IsContinuous_compose (incl_isContinuous A) Hf

def Subtopology.IsContinuousWithinAt [HX : Topology X] [HY : Topology Y] (f : X → Y) (A : Set X) (x : A) :=
  @IsContinuousAt _ _ (Subtopology A) _ (restrict f A) x


lemma Subtopology.locall_IsContinuousAt [HX : Topology X] [HY : Topology Y]
  (f : X → Y) (A : Set X) (x : A)
  (HA : A ∈ neighborOf x.val)
  (Hf : IsContinuousWithinAt f A x) :
  IsContinuousAt f x.val
:= by
  unfold IsContinuousWithinAt at Hf
  unfold IsContinuousAt at Hf ⊢
  simp [restrict, incl] at Hf
  intro U HU
  specialize Hf U HU
  rw [neighborOf_iff] at Hf
  rcases Hf with ⟨V, HV, VU⟩
  have H := neighborOf_inter HA HV
  unfold neighborOf NeighborOf at H ⊢; simp at H ⊢
  rcases H with ⟨W, HW, Wx, WA, WV⟩
  use W, HW, Wx
  intro w Hw; simp
  specialize WV Hw
  specialize WA Hw
  have : ⟨w, WA⟩ ∈ {x : A | ↑x ∈ V} := by grind
  apply VU at this; simp at this
  exact this

lemma Subtopology.pasting_openCverd_continuous [HX : Topology X] {I : Type _} (A : I → Set X) (HA : ⋃ i, interior (A i) = Set.univ)
  [HX' : Topology X'] (f : X → X') :
  (∀ i, IsContinuous (restrict f (A i))) → IsContinuous f
:= by
  intro H
  have H' := isOpen_iff_covered_isOpen A HA
  rw [IsContinuous_iff_IsOpen_preimage]
  intro U HU
  change _ ∈ HX.isOpen
  rw [H']
  intro i; rw [Subtopology.isOpen_eq]; simp
  specialize H i; rw [@IsContinuous_iff_IsOpen_preimage] at H
  specialize H U HU
  simp [restrict, incl] at H
  rw [Subtopology.isOpen_eq] at H
  rcases H with ⟨V, HV, E⟩
  use V, HV; rw [<- E]; ext x; simp

lemma Subtopology.pasting_ClosedCoverd_countinuous [HX : Topology X] {I : Type _} (A : I → Set X)
  (HA1 : LocallyFinite A) (HA2 : ⋃ i, A i = Set.univ) (HA3 : ∀ i, HX.isClosed (A i))
  [HX' : Topology X'] (f : X → X') :
  (∀ i, IsContinuous (restrict f (A i))) → IsContinuous f
:= by
  intro H
  have H' := isClosed_iff_covered_isClosed A HA1 HA2 HA3
  rw [IsContinuous_iff_IsClosed_preimage]
  intro U HU
  rw [H']
  intro i; rw [Subtopology.isClosed_iff]; simp
  specialize H i; rw [@IsContinuous_iff_IsClosed_preimage] at H
  specialize H U HU
  simp [restrict, incl] at H
  rw [Subtopology.isClosed_iff] at H
  rcases H with ⟨V, HV, E⟩
  use V, HV; rw [<- E]; ext x; simp

end Bourbaki
