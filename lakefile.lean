import Lake
open Lake DSL

package «curry-howard-correspondence» where
  -- add package configuration options here

lean_lib «CurryHowardCorrespondence» where
  -- add library configuration options here

@[default_target]
lean_exe «curry-howard-correspondence» where
  root := `Main
