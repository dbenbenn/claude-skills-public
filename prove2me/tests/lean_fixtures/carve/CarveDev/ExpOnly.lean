import CarveDev.ExpImpl

/-! # CarveDev.ExpOnly: a module made only of an `export` block

q142 (JointDickman_Counting_BilinearEnergy): `namespace OAI.JointDickman.BilinearEnergy / export
Problem337.VaughanBilinear (energy_identity …) / end`. Pieces calling `BilinearEnergy.energy_identity`
got the exported theorem's module but never this one: "Unknown identifier". -/

namespace CD.EX.Alias
export CD.EX.Impl (val val_eq)
end CD.EX.Alias
