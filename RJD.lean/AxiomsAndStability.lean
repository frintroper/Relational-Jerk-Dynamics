import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

namespace RJD

/-- 1D directional projection of node accelerations at discrete step n -/
def State (N : Nat) := Fin N -> Real

/-- Normalized unit impulse between node i and node k (excludes 0/0 self-interaction) -/
noncomputable def unitImpulse {N : Nat} (a : State N) (i k : Fin N) : Real :=
  if a k > a i then 1
  else if a k < a i then -1
  else 0

/-- Total discrete Jerk acting on node i -/
noncomputable def jerk {N : Nat} (a : State N) (i : Fin N) : Real :=
  Finset.univ.sum (fun k => unitImpulse a i k)

/-- Unit impulse is strictly antisymmetric -/
lemma unitImpulse_antisymm {N : Nat} (a : State N) (i k : Fin N) :
    unitImpulse a i k = - unitImpulse a k i := by
  unfold unitImpulse
  split_ifs <;> linarith

/-- Global conservation of Jerk momentum across all nodes -/
theorem total_jerk_zero {N : Nat} (a : State N) :
    Finset.univ.sum (fun i => jerk a i) = 0 := by
  unfold jerk
  have h : Finset.univ.sum (fun i => Finset.univ.sum (fun k => unitImpulse a i k)) =
           Finset.univ.sum (fun i => Finset.univ.sum (fun k => - unitImpulse a k i)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    exact unitImpulse_antisymm a i k
  rw [Finset.sum_comm] at h
  simp only [Finset.sum_neg_distrib] at h
  linarith

end RJD
