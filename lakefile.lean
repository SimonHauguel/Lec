import Lake
open Lake DSL

package Lec {
  -- add package configuration options here
}

lean_lib Lec {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lec {
  root := `Main
}
