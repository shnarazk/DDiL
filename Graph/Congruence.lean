import Graph.Base

partial def Graph.isCongruent_aux (g₁ g₂ : Graph) (r₁ r₂ : Ref): Bool :=
  match r₁.link, r₂.link with
    | none, none => r₁.grounded == r₂.grounded
    | none, some i =>
      let n := g₂.nodes[i]!
      isCongruent_aux g₁ g₂ r₁ n.li && isCongruent_aux g₁ g₂ r₁ n.hi
    | some i, none =>
      let n := g₁.nodes[i]!
      isCongruent_aux g₁ g₂ n.li r₂ && isCongruent_aux g₁ g₂ n.hi r₂
    | some i₁, some i₂ =>
      let n₁ := g₁.nodes[i₁]!
      let n₂ := g₂.nodes[i₂]!
      match compare g₁.nodes[i₁]!.varId g₂.nodes[i₂]!.varId with
        | Ordering.lt => isCongruent_aux g₁ g₂ n₁.li r₂ && isCongruent_aux g₁ g₂ n₁.hi r₂
        | Ordering.eq => isCongruent_aux g₁ g₂ n₁.li n₂.li && isCongruent_aux g₁ g₂ n₁.hi n₂.hi
        | Ordering.gt => isCongruent_aux g₁ g₂ r₁ n₂.li && isCongruent_aux g₁ g₂ r₁ n₂.hi

def Graph.isCongruent (g₁ g₂ : Graph): Bool :=
  Graph.isCongruent_aux g₁ g₂ (Ref.for g₁) (Ref.for g₂)
