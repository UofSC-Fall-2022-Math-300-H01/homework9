import Lake
open Lake DSL

package hw7 {
  -- add package configuration options here
}

lean_lib Hw7 {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe hw7 {
  root := `Main
}
