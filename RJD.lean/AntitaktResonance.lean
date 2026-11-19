import Mathlib.Data.Real.Basic

namespace RJD

def isAntitakt (a_curr a_next : Real) : Prop := a_next = - a_curr
def stepUpdate (a_curr J : Real) : Real := a_curr + J

theorem antitakt_resonance_ratio (a_curr a_next J : Real)
    (h_step : a_next = stepUpdate a_curr J)
    (h_anti : isAntitakt a_curr a_next) :
    J = - 2 * a_curr := by
  unfold stepUpdate isAntitakt at *
  linarith

theorem antitakt_magnitude_twice_radius (a_curr a_next J : Real)
    (h_step : a_next = stepUpdate a_curr J)
    (h_anti : isAntitakt a_curr a_next) :
    abs J = 2 * abs a_curr := by
  have hJ := antitakt_resonance_ratio a_curr a_next J h_step h_anti
  rw [hJ, abs_mul, abs_neg, abs_of_pos (by norm_num : (2 : Real) > 0)]

end RJD
