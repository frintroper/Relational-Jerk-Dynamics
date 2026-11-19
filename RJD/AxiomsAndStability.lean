namespace RJD

def State (N : Nat) := Fin N -> Int

def unitImpulse {N : Nat} (a : State N) (i k : Fin N) : Int :=
  if a k > a i then 1
  else if a k < a i then -1
  else 0

lemma unitImpulse_antisymm {N : Nat} (a : State N) (i k : Fin N) :
    unitImpulse a i k = - unitImpulse a k i := by
  unfold unitImpulse
  split
  · rename_i h1
    split
    · omega
    · split
      · rfl
      · omega
  · rename_i h1
    split
    · rename_i h2
      split
      · omega
      · rfl
    · split
      · omega
      · simp

end RJD
