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
  else if k = 2 then ParticleClass.MasslessBosonChain
  else if k = 3 then ParticleClass.SubPlanckRing
  else if k = 4 then ParticleClass.StableFermionSimplex 1
  else if k = 8 then ParticleClass.StableFermionSimplex 2
  else if k = 12 then ParticleClass.StableFermionSimplex 3
  else ParticleClass.FragmentedUnstable

theorem saturation_bound_no_heavy_fermions (k : Nat) (hk : k > 12) (gen : Nat) :
    classifyCluster k ≠ ParticleClass.StableFermionSimplex gen := by
  unfold classifyCluster
  have h1 : ¬ (k < 2) := by omega
  have h2 : ¬ (k = 2) := by omega
  have h3 : ¬ (k = 3) := by omega
  have h4 : ¬ (k = 4) := by omega
  have h8 : ¬ (k = 8) := by omega
  have h12 : ¬ (k = 12) := by omega
  simp [h1, h2, h3, h4, h8, h12]

theorem minimal_fermion_is_four :
    classifyCluster 4 = ParticleClass.StableFermionSimplex 1 := by
  rfl

end RJD

