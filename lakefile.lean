import Lake

open Lake DSL

package AddCombi where
  leanOptions := #[
    -- Prevent typos to be interpreted as new free variables
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    -- Pretty-print lambdas as `fun a ↦ b`
    ⟨`pp.unicode.fun, true⟩,
    -- Elide the types of proofs in terms
    ⟨`pp.proofs.withType, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target] lean_lib AddCombi
