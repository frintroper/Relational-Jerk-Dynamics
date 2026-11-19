namespace RJD

def sumSquares : Nat -> Nat
  | 0 => 0
  | n + 1 => sumSquares n + (n + 1) * (n + 1)

theorem six_times_sum_squares (N : Nat) :
    6 * sumSquares N = N * (N + 1) * (2 * N + 1) := by
  induction N with
  | zero =>
    rfl
  | succ n ih =>
    unfold sumSquares
    have h1 : 6 * (sumSquares n + (n + 1) * (n + 1)) = 6 * sumSquares n + 6 * ((n + 1) * (n + 1)) := by
      omega
    rw [h1, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
    have h_comm1 : (n + 1) * n = n * (n + 1) := Nat.mul_comm (n + 1) n
    have h_comm2 : (2 * n + 1) * n = n * (2 * n + 1) := Nat.mul_comm (2 * n + 1) n
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] at h_comm1 h_comm2
    omega

theorem two_thirds_projection_law (N : Nat) :
    3 * (2 * sumSquares N) = N * (N + 1) * (2 * N + 1) := by
  have h := six_times_sum_squares N
  omega

end RJD
