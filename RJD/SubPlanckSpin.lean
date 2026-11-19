namespace RJD

inductive RingID | RingA | RingB
  deriving Repr, DecidableEq

structure SpinState where
  ring : RingID
  pos  : Fin 3
  deriving Repr, DecidableEq

def advanceSpin (s : SpinState) : SpinState :=
  match s.ring, s.pos with
  | RingID.RingA, ⟨0, _⟩ => ⟨RingID.RingA, ⟨1, by omega⟩⟩
  | RingID.RingA, ⟨1, _⟩ => ⟨RingID.RingA, ⟨2, by omega⟩⟩
  | RingID.RingA, ⟨2, _⟩ => ⟨RingID.RingB, ⟨0, by omega⟩⟩
  | RingID.RingB, ⟨0, _⟩ => ⟨RingID.RingB, ⟨1, by omega⟩⟩
  | RingID.RingB, ⟨1, _⟩ => ⟨RingID.RingB, ⟨2, by omega⟩⟩
  | RingID.RingB, ⟨2, _⟩ => ⟨RingID.RingA, ⟨0, by omega⟩⟩

def iterateSpin : Nat -> SpinState -> SpinState
  | 0, s => s
  | n + 1, s => advanceSpin (iterateSpin n s)

theorem spin_half_360_inverts :
    let s0 : SpinState := ⟨RingID.RingA, ⟨0, by omega⟩⟩
    iterateSpin 3 s0 = ⟨RingID.RingB, ⟨0, by omega⟩⟩ := by
  rfl

theorem spin_half_720_restores :
    let s0 : SpinState := ⟨RingID.RingA, ⟨0, by omega⟩⟩
    iterateSpin 6 s0 = s0 := by
  rfl

end RJD

