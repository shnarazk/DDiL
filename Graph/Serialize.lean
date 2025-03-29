import Graph.Basic

def Graph.dumpAsDot (self : Graph) (path : String) (title : String := path) : IO String := do
  let buffer := s!"digraph regexp \{
    label=\"{title}\"
    fontname=\"Helvetica,Arial,sans-serif\"
    node [fontname=\"Helvetica,Arial,sans-serif\"]
    edge [fontname=\"Helvetica,Arial,sans-serif\", color=blue]
      0 [style=filled, fillcolor=\"gray80\",label=\"false\",shape=\"box\"];
      1 [style=filled, fillcolor=\"gray95\",label=\"true\",shape=\"box\"];
  "
  let nodes := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦  s!"  {i + 2} [label=\"{node.varId}\"];\n")
    |> String.join
  let edges := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦
        let li := match node.li.link, node.li.grounded with
          | none, false => 0
          | none, true  => 1
          | some i, _   => i + 2
        let hi := match node.hi.link, node.hi.grounded with
          | none, false => 0
          | none, true  => 1
          | some i, _   => i + 2
        if li == hi then
              s!" {i + 2} -> {li} [color=black,penwidth=2];\n"
            else
              s!" {i + 2} -> {li} [color=red,style=\"dotted\"];\n" ++
              s!" {i + 2} -> {hi} [color=blue];\n" )
    |> String.join
  IO.FS.writeFile path (buffer ++ "\n" ++ nodes ++ "\n" ++ edges ++ "\n}\n")
  return path

def Graph.dumpAsPng (self : Graph) (path : String) (title : String := path) : IO String := do
  try
    let gv := s!"{path}.gv"
    let _ ← self.dumpAsDot gv title
    let _ ← IO.Process.run { cmd := "dot", args := #["-T", "png", "-o", path, gv]}
    IO.FS.removeFile gv
    return path
  catch e =>
    return s!"Error dumping graph to PNG: {e}"

instance : GraphSerialize Graph where
  dumpAsDot := Graph.dumpAsDot
  dumpAsPng := Graph.dumpAsPng
