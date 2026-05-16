import Lake
open Lake DSL

package «adic_lean_qdd_replay» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib «ADIC_RSound_Replay» where

@[default_target]
lean_lib «ADIC_QuantumDrugDiscovery» where
