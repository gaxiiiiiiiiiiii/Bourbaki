import Bourbaki.Topology.ch1_topology.ss1
import Bourbaki.Topology.ch1_topology.ss2
import Bourbaki.Topology.ch1_topology.ss3_1_subspace

namespace Bourbaki
#check IsContinuous

def Subtopology.incl [Topology X] (A : Set X) : A → X := Subtype.val

def Subtopology.incl_isContinuous [HX : Topology X] (A : Set X) :
  @IsContinuous A X (Subtopology A) HX (incl A )
:= Init.isContinuous (fun _ : PUnit.{1} => (Function.Embedding.subtype A).1) PUnit.unit

def Subtopology.restrict [HX : Topology X] (f : X → Y) (A : Set X) : A → Y := f ∘ incl A

lemma Subtopology.restrict_isContinuous [HX : Topology X] [HY : Topology Y]
  {A : Set X} {f : X → Y} (Hf : IsContinuous f) :
  @IsContinuous A Y (Subtopology A) HY (restrict f A)
:= @IsContinuous_compose _ _ _ (Subtopology A) _ _ _ _ (incl_isContinuous A) Hf

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




























end Bourbaki
