namespace RJD

def State (N : Nat) := Fin N -> Int

def unitImpulse {N : Nat} (a : State N) (i k : Fin N) : Int :=
  if a k > a i then
    (1 : Int)
  else
    if a k < a i then (-1 : Int) else (0 : Int)

theorem unitImpulse_antisymm {N : Nat} (a : State N) (i k : Fin N) :
    unitImpulse a i k = - unitImpulse a k i := by
  unfold unitImpulse
  by_cases h1 : a k > a i
  · have h2 : ¬ (a i > a k) := by omega
    have h3 : a i < a k := by omega
    simp [h1, h2, h3]
  · by_cases h2 : a k < a i
    · have h3 : a i > a k := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (a i > a k) := by omega
      have h4 : ¬ (a i < a k) := by omega
      simp [h1, h2, h3, h4]

end RJD
