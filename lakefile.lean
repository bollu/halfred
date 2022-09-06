import Lake
open Lake DSL

package «Halfred»

@[defaultTarget]
lean_exe «halfred-flowchart» {
  root := `Flowchart
  supportInterpreter := true
}

