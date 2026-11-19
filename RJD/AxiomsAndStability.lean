namespace RJD

/-- Discrete directional unit impulse between two relational states -/
def impulse (a_i a_k : Int) : Int :=
  if a_k > a_i then (1 : Int)
  else if a_k < a_i then (-1 : Int)
  else (0 : Int)

/-- Total discrete Jerk acting on state a_i from an entire network list -/
def totalJerk (a_i : Int) : List Int -> Int
  | [] => 0
  | x :: xs => impulse a_i x + totalJerk a_i xs

/-- Lemma 1: Antisymmetry of pairwise relational impulses -/
theorem impulse_antisymm (x y : Int) :
    impulse x y = - impulse y x := by
  unfold impulse
  by_cases h1 : y > x
  · have h2 : ¬ (x > y) := by omega
    have h3 : x < y := by omega
    simp [h1, h2, h3]
  · by_cases h2 : y < x
    · have h3 : x > y := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (x > y) := by omega
      have h4 : ¬ (x < y) := by omega
      simp [h1, h2, h3, h4]

/-- Lemma 2: Every individual impulse is bounded in [-1, 1] -/
theorem impulse_bounds (x y : Int) :
    -1 <= impulse x y ∧ impulse x y <= 1 := by
  unfold impulse
  by_cases h1 : y > x
  · simp [h1]
  · by_cases h2 : y < x
    · simp [h1, h2]
    · simp [h1, h2]

/-- Theorem (Ostrogradski Stabilization): Total jerk is strictly bounded by network size N -/
theorem ostrogradski_jerk_bound (a_i : Int) (net : List Int) :
    -(net.length : Int) <= totalJerk a_i net ∧ totalJerk a_i net <= (net.length : Int) := by
  induction net with
  | nil =>
    simp [totalJerk]
  | head tail ih =>
    simp only [totalJerk, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hb := impulse_bounds a_i head
    omega

/-- Helper: If a_max dominates every element in net, totalJerk is non-positive -/
theorem extremal_jerk_nonpos (a_max : Int) (net : List Int)
    (h_max : forall x, x ∈ net -> x <= a_max) :
    totalJerk a_max net <= 0 := by
  induction net with
  | nil =>
    simp [totalJerk]
  | head tail ih =>
    simp only [totalJerk]
    have h_head : head <= a_max := h_max head (List.mem_cons_self _ _)
    have h_imp : impulse a_max head <= 0 := by
      unfold impulse
      have h_not_gt : ¬ (head > a_max) := by omega
      by_cases h_lt : head < a_max
      · simp [h_not_gt, h_lt]
      · simp [h_not_gt, h_lt]
    have h_tail : totalJerk a_max tail <= 0 := by
      apply ih
      intro x hx
      exact h_max x (List.mem_cons_of_mem _ hx)
    omega

/-- THEOREM 1 (Singularity Avoidance / No Global Equilibrium):
    If a_max is an extremal state and there exists at least one distinct state y in the network,
    the total Jerk on a_max is strictly negative (hence non-zero). -/
theorem extremal_node_nonzero_jerk (a_max : Int) (net : List Int)
    (h_max : forall x, x ∈ net -> x <= a_max)
    (h_exists_distinct : exists y, y ∈ net ∧ y ≠ a_max) :
    totalJerk a_max net < 0 := by
  induction net with
  | nil =>
    rcases h_exists_distinct with ⟨y, hy, _⟩
    cases hy
  | head tail ih =>
    simp only [totalJerk]
    have h_head_le : head <= a_max := h_max head (List.mem_cons_self _ _)
    have h_tail_max : forall x, x ∈ tail -> x <= a_max := by
      intro x hx
      exact h_max x (List.mem_cons_of_mem _ hx)
    by_cases h_head_ne : head ≠ a_max
    · -- Case 1: head itself is strictly smaller than a_max
      have h_head_lt : head < a_max := by omega
      have h_imp_neg : impulse a_max head = -1 := by
        unfold impulse
        have h1 : ¬ (head > a_max) := by omega
        simp [h1, h_head_lt]
      have h_tail_nonpos : totalJerk a_max tail <= 0 := extremal_jerk_nonpos a_max tail h_tail_max
      omega
    · -- Case 2: head = a_max, so the distinct element must lie in tail
      have h_imp_zero : impulse a_max head = 0 := by
        unfold impulse
        have h1 : ¬ (head > a_max) := by omega
        have h2 : ¬ (head < a_max) := by omega
        simp [h1, h2]
      have h_tail_distinct : exists y, y ∈ tail ∧ y ≠ a_max := by
        rcases h_exists_distinct with ⟨y, hy_mem, hy_ne⟩
        cases hy_mem with
        | head => contradiction
        | tail _ h_in_tail => exact ⟨y, h_in_tail, hy_ne⟩
      have h_tail_neg : totalJerk a_max tail < 0 := ih h_tail_max h_tail_distinct
      omega

end RJD
