namespace RJD

def isAntitakt (a_curr a_next : Int) : Prop := a_next = - a_curr
def stepUpdate (a_curr J : Int) : Int := a_curr + J

theorem antitakt_resonance_ratio (a_curr a_next J : Int)
    (h_step : a_next = stepUpdate a_curr J)
    (h_anti : isAntitakt a_curr a_next) :
    J = - 2 * a_curr := by
  unfold stepUpdate isAntitakt at *
  omega

end RJD
