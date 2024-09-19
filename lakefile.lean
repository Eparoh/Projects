import Lake
open Lake DSL

package «Projects» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FunctionalAnalysis» where

@[default_target]
lean_lib «Topology» where

@[default_target]
lean_lib «Aprendizaje» where
