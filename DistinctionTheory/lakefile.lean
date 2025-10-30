import Lake
open Lake DSL

package «distinction_theory» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «DistinctionTheory» where
  root := `DistinctionTheory