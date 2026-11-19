namespace RJD

def impulse (a_i a_k : Int) : Int :=
  if a_k > a_i then (1 : Int)
  else if a_k < a_i then (-1 : Int)
  else (0 : Int)

def totalJerk (a_i : Int) : List Int -> Int
  | [] => 0
  | x :: xs => impulse a_i x + totalJerk a_i xs

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

theorem impulse_bounds (x y : Int) :
    -1 <= impulse x y ∧ impulse x y <= 1 := by
  unfold impulse
  by_cases h1 : y > x
  · simp [h1]
  · by_cases h2 : y < x
    · simp [h1, h2]
    · simp [h1, h2]

theorem ostrogradski_jerk_bound (a_i : Int) (net : List Int) :
    -(net.length : Int) <= totalJerk a_i net ∧ totalJerk a_i net <= (net.length : Int) := by
  induction net with
  | nil =>
    simp [totalJerk]
  | cons x xs ih =>
    simp only [totalJerk, List.length_cons, Int.ofNat_add, Int.ofNat_succ, Int.ofNat_zero]
    have hb := impulse_bounds a_i x
    omega

theorem extremal_jerk_nonpos (a_max : Int) (net : List Int)
    (h_max : forall x, x ∈ net -> x <= a_max) :
    totalJerk a_max net <= 0 := by
  induction net with
  | nil =>
    simp [totalJerk]
  | cons x xs ih =>
    simp only [totalJerk]
    have h_head : x <= a_max := h_max x (List.mem_cons_self _ _)
    have h_imp : impulse a_max x <= 0 := by
      unfold impulse
      have h_not_gt : ¬ (x > a_max) := by omega
      by_cases h_lt : x < a_max
      · simp [h_not_gt, h_lt]
      · simp [h_not_gt, h_lt]
    have h_tail : totalJerk a_max xs <= 0 := by
      apply ih
      intro z hz
      exact h_max z (List.mem_cons_of_mem _ hz)
    omega

theorem extremal_node_nonzero_jerk (a_max : Int) (net : List Int)
    (h_max : forall x, x ∈ net -> x <= a_max)
    (h_exists_distinct : exists y, y ∈ net ∧ y ≠ a_max) :
    totalJerk a_max net < 0 := by
  induction net with
  | nil =>
    rcases h_exists_distinct with ⟨y, hy, _⟩
    cases hy
  | cons x xs ih =>
    simp only [totalJerk]
    have h_head_le : x <= a_max := h_max x (List.mem_cons_self _ _)
    have h_tail_max : forall z, z ∈ xs -> z <= a_max := by
      intro z hz
      exact h_max z (List.mem_cons_of_mem _ hz)
    by_cases h_head_ne : x ≠ a_max
    · have h_head_lt : x < a_max := by omega
      have h_imp_neg : impulse a_max x = -1 := by
        unfold impulse
        have h1 : ¬ (x > a_max) := by omega
        simp [h1, h_head_lt]
      have h_tail_nonpos : totalJerk a_max xs <= 0 := extremal_jerk_nonpos a_max xs h_tail_max
      omega
    · have h_imp_zero : impulse a_max x = 0 := by
        unfold impulse
        have h1 : ¬ (x > a_max) := by omega
        have h2 : ¬ (x < a_max) := by omega
        simp [h1, h2]
      have h_tail_distinct : exists y, y ∈ xs ∧ y ≠ a_max := by
        rcases h_exists_distinct with ⟨y, hy_mem, hy_ne⟩
        cases hy_mem with
        | head => contradiction
        | tail _ h_in_tail => exact ⟨y, h_in_tail, hy_ne⟩
      have h_tail_neg : totalJerk a_max xs < 0 := ih h_tail_max h_tail_distinct
      omega

end RJD
