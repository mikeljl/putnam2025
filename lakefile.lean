
import Lake
open Lake DSL

package «putnam2025» where
  -- add any additional package configuration options here

require mathlib from git
   "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"

@[default_target]
lean_lib «Putnam2025» where
  -- add any library configuration options here

