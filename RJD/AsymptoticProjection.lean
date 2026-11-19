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
    have h_step : n * (2 * n + 1) + 6 * (n + 1) = (n + 2) * (2 * n + 3) := by
      simp only [Nat.mul_add, Nat.add_mul]
      have h_comm : 2 * n * n = n * (2 * n) := by
        rw [Nat.mul_comm (2 * n) n]
      omega
    calc
      n * (n + 1) * (2 * n + 1) + 6 * ((n + 1) * (n + 1))
        = (n + 1) * (n * (2 * n + 1)) + (n + 1) * (6 * (n + 1)) := by
            rw [Nat.mul_comm n (n + 1), Nat.mul_assoc (n + 1) n (2 * n + 1), Nat.mul_left_comm 6 (n + 1) (n + 1)]
      _ = (n + 1) * (n * (2 * n + 1) + 6 * (n + 1)) := by
            rw [← Nat.mul_add]
      _ = (n + 1) * ((n + 2) * (2 * n + 3)) := by
            rw [h_step]
      _ = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by
            rw [← Nat.mul_assoc]
            rfl

theorem two_thirds_projection_law (N : Nat) :
    3 * (2 * sumSquares N) = N * (N + 1) * (2 * N + 1) := by
  have h := six_times_sum_squares N
  omega

end RJD
