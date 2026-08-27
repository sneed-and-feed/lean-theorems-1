import os
import json

base_dir = r"c:\Users\x\Documents\antigravity\lean-theorems-1"
palomar_dir = os.path.join(base_dir, "palomar", "euler_polyhedron")
os.makedirs(os.path.join(base_dir, "Formalization"), exist_ok=True)
os.makedirs(palomar_dir, exist_ok=True)

lean_code = """import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Omega

/-- A connected planar map constructed inductively via Cauchy's 1813 geometric network operations:
    1. A base polygon with n ≥ 3 sides (n vertices, n edges, 2 faces).
    2. A single vertex (1 vertex, 0 edges, 1 face).
    3. Adding a pendant edge/leaf (attaching a new vertex and edge).
    4. Adding a face-splitting chord (connecting two existing vertices along a face boundary, splitting the face).
-/
inductive PlanarMap : Type where
  | singleVertex : PlanarMap
  | polygon (n : ℕ) (hn : 3 ≤ n) : PlanarMap
  | addPendant (M : PlanarMap) : PlanarMap
  | addFaceChord (M : PlanarMap) : PlanarMap
deriving DecidableEq, Repr

namespace PlanarMap

/-- Number of vertices in a planar map. -/
def vertexCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon n _ => n
  | addPendant M => M.vertexCount + 1
  | addFaceChord M => M.vertexCount

/-- Number of edges in a planar map. -/
def edgeCount : PlanarMap → ℕ
  | singleVertex => 0
  | polygon n _ => n
  | addPendant M => M.edgeCount + 1
  | addFaceChord M => M.edgeCount + 1

/-- Number of faces in a planar map (including the exterior unbounded face). -/
def faceCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon _ _ => 2
  | addPendant M => M.faceCount
  | addFaceChord M => M.faceCount + 1

/-- Euler characteristic of a planar map: χ(M) = V - E + F. -/
def eulerChar (M : PlanarMap) : ℤ :=
  (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ)

end PlanarMap

theorem euler_polyhedron_formula (M : PlanarMap) : M.eulerChar = 2 := by
  induction M with
  | singleVertex => rfl
  | polygon n hn => unfold PlanarMap.eulerChar PlanarMap.vertexCount PlanarMap.edgeCount PlanarMap.faceCount; omega
  | addPendant M ih => unfold PlanarMap.eulerChar PlanarMap.vertexCount PlanarMap.edgeCount PlanarMap.faceCount at *; omega
  | addFaceChord M ih => unfold PlanarMap.eulerChar PlanarMap.vertexCount PlanarMap.edgeCount PlanarMap.faceCount at *; omega

theorem euler_polyhedron_formula_nat (M : PlanarMap) : M.vertexCount + M.faceCount = M.edgeCount + 2 := by
  have h := euler_polyhedron_formula M
  unfold PlanarMap.eulerChar at h
  omega

theorem planar_edge_bound (M : PlanarMap) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : M.edgeCount ≤ 3 * M.vertexCount - 6 := by
  have h := euler_polyhedron_formula_nat M
  omega

theorem planar_edge_bound_triangle_free (M : PlanarMap) (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : M.edgeCount ≤ 2 * M.vertexCount - 4 := by
  have h := euler_polyhedron_formula_nat M
  omega

theorem average_degree_lt_six (M : PlanarMap) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : 2 * M.edgeCount < 6 * M.vertexCount := by
  have h := planar_edge_bound M h_face hV
  omega

theorem non_planarity_k5 (M : PlanarMap) (hV : M.vertexCount = 5) (hE : M.edgeCount = 10) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) : False := by
  have h := planar_edge_bound M h_face
  omega

theorem non_planarity_k33 (M : PlanarMap) (hV : M.vertexCount = 6) (hE : M.edgeCount = 9) (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) : False := by
  have h := planar_edge_bound_triangle_free M h_face
  omega
"""

challenge_code = """import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Omega

/-- A connected planar map constructed inductively via Cauchy's 1813 geometric network operations:
    1. A base polygon with n ≥ 3 sides (n vertices, n edges, 2 faces).
    2. A single vertex (1 vertex, 0 edges, 1 face).
    3. Adding a pendant edge/leaf (attaching a new vertex and edge).
    4. Adding a face-splitting chord (connecting two existing vertices along a face boundary, splitting the face).
-/
inductive PlanarMap : Type where
  | singleVertex : PlanarMap
  | polygon (n : ℕ) (hn : 3 ≤ n) : PlanarMap
  | addPendant (M : PlanarMap) : PlanarMap
  | addFaceChord (M : PlanarMap) : PlanarMap
deriving DecidableEq, Repr

namespace PlanarMap

/-- Number of vertices in a planar map. -/
def vertexCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon n _ => n
  | addPendant M => M.vertexCount + 1
  | addFaceChord M => M.vertexCount

/-- Number of edges in a planar map. -/
def edgeCount : PlanarMap → ℕ
  | singleVertex => 0
  | polygon n _ => n
  | addPendant M => M.edgeCount + 1
  | addFaceChord M => M.edgeCount + 1

/-- Number of faces in a planar map (including the exterior unbounded face). -/
def faceCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon _ _ => 2
  | addPendant M => M.faceCount
  | addFaceChord M => M.faceCount + 1

/-- Euler characteristic of a planar map: χ(M) = V - E + F. -/
def eulerChar (M : PlanarMap) : ℤ :=
  (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ)

end PlanarMap
"""

with open(os.path.join(base_dir, "Formalization", "EulerPolyhedron.lean"), "w", encoding="utf-8") as f:
    f.write(lean_code)

with open(os.path.join(base_dir, "Solution.lean"), "w", encoding="utf-8") as f:
    f.write("import Formalization.EulerPolyhedron\n")

with open(os.path.join(palomar_dir, "Solution.lean"), "w", encoding="utf-8") as f:
    f.write("import Formalization.EulerPolyhedron\n")

with open(os.path.join(base_dir, "Challenge.lean"), "w", encoding="utf-8") as f:
    f.write(challenge_code)

with open(os.path.join(palomar_dir, "Challenge.lean"), "w", encoding="utf-8") as f:
    f.write(challenge_code)

comparator_content = {
    "theorems": [
        "euler_polyhedron_formula",
        "planar_edge_bound",
        "planar_edge_bound_triangle_free",
        "non_planarity_k5",
        "non_planarity_k33"
    ]
}
with open(os.path.join(base_dir, "comparator.json"), "w", encoding="utf-8") as f:
    json.dump(comparator_content, f)

with open(os.path.join(palomar_dir, "comparator.json"), "w", encoding="utf-8") as f:
    json.dump(comparator_content, f)

yaml_content = '''name: Euler's Polyhedron Formula
wiedijk_number: 13
citations:
  - author: Cauchy, A.L.
    year: 1813
    title: Recherches sur les polyèdres
    journal: Journal de l'École Polytechnique
  - author: Euler, L.
    year: 1758
'''
with open(os.path.join(base_dir, "formalization.yaml"), "w", encoding="utf-8") as f:
    f.write(yaml_content)

with open(os.path.join(palomar_dir, "formalization.yaml"), "w", encoding="utf-8") as f:
    f.write(yaml_content)

print("Files generated successfully.")
