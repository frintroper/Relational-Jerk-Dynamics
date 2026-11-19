namespace RJD

inductive ParticleClass
  | InvalidVacuum
  | MasslessBosonChain
  | SubPlanckRing
  | StableFermionSimplex (generation : Nat)
  | FragmentedUnstable
  deriving Repr, DecidableEq

def classifyCluster (k : Nat) : ParticleClass :=
  if k < 2 then ParticleClass.InvalidVacuum
  else if k == 2 then ParticleClass.MasslessBosonChain
  else if k == 3 then ParticleClass.SubPlanckRing
  else if k == 4 then ParticleClass.StableFermionSimplex 1
  else if k == 8 then ParticleClass.StableFermionSimplex 2
  else if k == 12 then ParticleClass.StableFermionSimplex 3
  else ParticleClass.FragmentedUnstable

theorem saturation_bound_no_heavy_fermions (k : Nat) (hk : k > 12) :
    forall gen, classifyCluster k ≠ ParticleClass.StableFermionSimplex gen := by
  intro gen h_eq
  unfold classifyCluster at h_eq
  split at h_eq <;> try contradiction
  split at h_eq <;> try contradiction
  split at h_eq <;> try contradiction
  split at h_eq <;> try omega
  split at h_eq <;> try omega
  split at h_eq <;> try omega
  contradiction

theorem minimal_fermion_is_four :
    classifyCluster 4 = ParticleClass.StableFermionSimplex 1 := by
  rfl

end RJD

