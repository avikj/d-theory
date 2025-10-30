import Lake
open Lake DSL

package «distinction_lean» where
  -- add package configuration options here

lean_lib «DistinctionLean» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «distinction_lean» where
  root := `Main
