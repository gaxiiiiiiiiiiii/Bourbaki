import Mathlib

namespace Bourbaki

@[ext]
structure InvSystem [Preorder I] (E : I → Type k)  where
  map {i j} : i ≤ j →  E j → E i
  map_id : ∀ i, map (le_refl i) = id
  map_comp : ∀ {i j k} (Hij : i ≤ j) (Hjk : j ≤ k),
     map Hij ∘ map Hjk = map (le_trans Hij Hjk)

@[simp]
def InvSystem.limit [Preorder I] {E : I → Type _}  (S : InvSystem E) :=
  {f : Π i, E i | ∀ i j (H : i ≤ j), f i = S.map H (f j)}

def InvSystem.proj  [Preorder I] {E : I → Type _} (S : InvSystem E) (i : I) :
  limit S → E i
:= fun f => f.val i

def InvSystem.sub [Preorder I] {E : I → Type _} (S : InvSystem E) (J : Set I) :
  InvSystem (fun j : J => E j.val)
where
  map {i j} H := by
    apply S.map (H : i.val ≤ j.val)
  map_id := by
    intro i; rw [S.map_id]
  map_comp := by
    intro i j k (Hij : i.val ≤ j.val) (Hjk : j.val ≤ k.val)
    rw [S.map_comp Hij Hjk]

def InvSystem.subMap [Preorder I] {E : I → Type _} (S : InvSystem E) (J : Set I) :
  S.limit → (S.sub J).limit
:= fun f  => by
  use fun j => f.val j.val
  simp [InvSystem.sub]; intro i Hi j Hj H
  have E := f.prop i j H
  rw [E]


lemma InvSystem.subMap_comp [Preorder I] {E : I → Type _} (S : InvSystem E) (J : Set I) (J' : Set J) (x : S.limit) (i : J') :
  (S.subMap (Subtype.val '' J') x).val ⟨i.val.val, by simp⟩ = (((S.sub J).subMap J' ∘ S.subMap J) x).val i
:= by
  simp [InvSystem.subMap]
