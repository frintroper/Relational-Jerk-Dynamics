namespace RJD

def expectedNextSqSeparation (D_sq sigma_sq : Nat) : Nat :=
  D_sq + sigma_sq

theorem cosmological_overshoot_expansion (D_sq sigma_sq : Nat)
    (h_var : sigma_sq > 0) :
    expectedNextSqSeparation D_sq sigma_sq > D_sq := by
  unfold expectedNextSqSeparation
  omega

def iterateExpansion : Nat -> Nat -> Nat -> Nat
  | 0, D_sq, _ => D_sq
  | k + 1, D_sq, sigma_sq => expectedNextSqSeparation (iterateExpansion k D_sq sigma_sq) sigma_sq

theorem multi_step_expansion (k D_sq sigma_sq : Nat) :
    iterateExpansion k D_sq sigma_sq = D_sq + k * sigma_sq := by
  induction k with
  | zero =>
    unfold iterateExpansion
    omega
  | succ n ih =>
    unfold iterateExpansion expectedNextSqSeparation
    rw [ih]
    omega

structure MesonState where
  k_heavy : Nat
  k_light : Nat

structure DileptonState where
  k_lep1 : Nat
  k_lep2 : Nat

theorem bd_to_mumu_node_conservation :
    let bd : MesonState := { k_heavy := 12, k_light := 4 }
    let mumu : DileptonState := { k_lep1 := 8, k_lep2 := 8 }
    bd.k_heavy + bd.k_light = mumu.k_lep1 + mumu.k_lep2 := by
  rfl

end RJD

