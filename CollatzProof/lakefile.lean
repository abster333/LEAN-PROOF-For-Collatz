import Lake
open Lake DSL

package «CollatzProof» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.2.0"

@[default_target]
lean_lib «CollatzProof»
