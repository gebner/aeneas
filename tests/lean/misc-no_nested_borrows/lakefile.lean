import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «no_nested_borrows» {}

lean_lib «Base» {}

@[default_target]
lean_lib «NoNestedBorrows» {}
