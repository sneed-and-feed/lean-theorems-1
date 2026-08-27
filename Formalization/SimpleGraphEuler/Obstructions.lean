import Formalization.SimpleGraphEuler.TreeEuler

open SimpleGraph

namespace SimpleGraphEuler

/-- Non-planarity obstruction for K5: complete graph on 5 vertices cannot admit a planar embedding. -/
theorem non_planarity_k5
    (emb : PlanarEmbedding (completeGraph (Fin 5)))
    (h_face : 3 * emb.faceCount ≤ 2 * (completeGraph (Fin 5)).edgeFinset.card) :
    False := by
  have h_bound := planar_edge_bound (completeGraph (Fin 5)) emb h_face (by decide)
  have hV : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hE : (completeGraph (Fin 5)).edgeFinset.card = 10 := by decide
  omega

instance (V W : Type*) [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro x y
  unfold completeBipartiteGraph
  infer_instance

/-- Non-planarity obstruction for K3,3: complete bipartite graph K_{3,3} cannot admit a triangle-free planar embedding. -/
theorem non_planarity_k33
    (emb : PlanarEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)))
    (h_face : 4 * emb.faceCount ≤ 2 * (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card) :
    False := by
  have h_bound := planar_edge_bound_triangle_free (completeBipartiteGraph (Fin 3) (Fin 3)) emb h_face (by decide)
  have hV : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by decide
  have hE : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card = 9 := by decide
  omega

end SimpleGraphEuler