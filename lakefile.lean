import Lake
open Lake DSL

package hw9 {
  -- add package configuration options here
}

lean_lib Sets {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe hw9 {
  root := `Main
}
