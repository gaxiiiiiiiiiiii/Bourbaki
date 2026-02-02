import Mathlib


section saturated

def IsSaturated {X Y : Type _} (f : X → Y) (V : Set X) :=
  ∀ x ∈ V, ∀ y, (Setoid.ker f).r x y → y ∈ V

lemma IsSaturated_iff_eq_preimage_image (f : X → Y) (V : Set X) :
  IsSaturated f V ↔ ((Quotient.mk (Setoid.ker f)) ⁻¹' (Quotient.mk (Setoid.ker f) '' V)) = V
:= by
  unfold IsSaturated
  constructor<;>  intro H
  · ext x; simp
    constructor<;> intro Hx
    · rcases Hx with ⟨y, Hy, E⟩
      rw [Quotient.eq] at E
      apply H y Hy x E
    · use x
  · intro x Hx y E; simp at E
    rw [<- H]; simp
    use x, Hx
    rw [Quotient.eq]; exact E

lemma IsSaturated_iff_coverd (f : X → Y) (V : Set X) :
  IsSaturated f V ↔ V = ⋃ v ∈ V, {x | (Setoid.ker f).r v x}
:= by
  simp [IsSaturated]
  constructor<;> intro H
  · ext x; simp
    constructor<;> intro Hx; grind
    rcases Hx with ⟨y, Hy, E⟩
    apply H y Hy x E
  · intro x Hx y E
    rw [H]; simp
    use x, Hx, E

end saturated
