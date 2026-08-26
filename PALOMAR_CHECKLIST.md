# Palomar Submission Master Priority Queue: Repo 1

All 33 theorems have completed exhaustive pre-flight self-audits according to `palomar-registry-workflow` SOP.
- **Live / Processed Entries**: Historical registered commit SHAs and live Palomar registry URLs are permanently preserved.
- **Unsubmitted Queue**: Each theorem has its own dedicated, immutable 40-character Git commit SHA with its specific package active at root.

### Submission Settings for submit.palomar-registry.org:
- **Repository**: `sneed-and-feed/lean-theorems-1`
- **Comparator Path**: `palomar/<slug>/comparator.json` *(or `comparator.json`)*
- **Existing Palomar ID**: *(leave blank)*
- **Relationship**: `Maintainer` / `Author`

---

## 🟢 Live & Registered Entries (Historical SHAs Intact)

| # | Theorem Title | Registered Commit SHA | Live Palomar Registry Entry | Status |
| :---: | :--- | :--- | :--- | :---: |
| **1** | **Desargues's Theorem (Synthetic Projective Equivalence)** | `bd8d660839c25d5ab93f3660c06141e98d15e978` | *(did not meet research floor)* | [-] **REJECTED** |
| **2** | **Graham–Pollak Theorem & Star Tightness** | `8b5a302a0b5136e2f0b3fdd4823e7ed8e190e839` | [PALOMAR-2026-08-26-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-08-26-000001) | [x] **LIVE** |
| **3** | **Bondy's Theorem on Induced Subsets** | `0e0b6bd4466f81c26df99f38eb43ae26dc080f00` | [PALOMAR-2026-08-26-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-08-26-000007) | [x] **LIVE** |
| **4** | **Bollobás's Two Families Theorem (Set Pairs)** | `38161dacae52fb604fb26933140dd4c3a129369d` | [PALOMAR-2026-08-26-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-26-000008) | [x] **LIVE** |
| **11** | **Erdős–Ko–Rado & Hilton–Milner Extremizer** | `158e3dbad77b780e4e21c89072bc3b863104edd1` | [PALOMAR-2026-08-26-000009](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-26-000009) | [x] **LIVE** |
| **14** | **The Friendship Theorem (Unique Common Neighbors)** | `f60794e58faf3eb7032a78f7e756538cb6513da5` | [PALOMAR-2026-08-26-000011](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-26-000011) | [x] **LIVE** |

---

## 🚀 Priority Submission Queue (Audited Unsubmitted Theorems)

| Priority # | Theorem / Package Title | Wiedijk # | Dedicated Commit SHA to Enter | Comparator Path | Status |
| :---: | :--- | :---: | :--- | :--- | :---: |
| | **Tier 1: Crown Jewels** | | | | |
| **1** | **Euler's Polyhedron Formula (V - E + F = 2)** | #13 | `c0f37d0ead18b016dab6012537b172eee7656f50` | `palomar/euler_polyhedron/comparator.json` | [ ] Pending Refactor (Rotation Systems in `cb78c945`) |
| **2** | **Sylvester–Gallai Theorem (Ordinary Lines)** | #98 | `35f4023fda8c9a37287dea03fe9f3487649c919a` | `palomar/sylvester_gallai/comparator.json` | [ ] Ready |
| **3** | **Hall's Marriage Theorem (Matching SDRs)** | #87 | `3d51e2aeae59cee1fb27385bbff30118b97161a9` | `palomar/hall_marriage/comparator.json` | [ ] Ready |
| **4** | **Sperner's Lemma in 1D and 2D** | #57 | `63e3a2ab5707b10d0f5eced32df02ba772009e17` | `palomar/sperners_lemma/comparator.json` | [ ] Ready |
| **5** | **Descartes's Rule of Signs** | #73 | `ea50c82e5f516bca8c0039ad2dd9ffbb991cc2ea` | `palomar/descartes_rule_of_signs/comparator.json` | [ ] Ready |
| **6** | **Radon's Lemma & Helly's Theorem** | #99 | `82a0ab6ae2533f5f8d33f323342da2d5e1254653` | `palomar/radon_helly/comparator.json` | [ ] Ready |
| **7** | **Pick's Theorem on Lattice Polygons** | #92 | `51489f83dae3c803170f81cb39859fcbb40d69d9` | `palomar/picks_theorem/comparator.json` | [ ] Ready |
| | **Tier 2: Celebrated Combinatorics** | | | | |
| **8** | **Chvátal's Art Gallery Theorem (Fisk's 3-Coloring)** | — | `5c54de28ba10fd5b6927936c139a02d575819c0e` | `palomar/art_gallery_theorem/comparator.json` | [ ] Ready |
| **9** | **Erdős–Szekeres Convex Polygon (Happy Ending 1935)** | — | `f13f3ca203775ae12ffaf9cee818f7f1073eef7f` | `palomar/erdos_szekeres_convex/comparator.json` | [ ] Ready |
| **10** | **The Crossing Lemma (Ajtai et al. / Leighton 1982)** | — | `fa7a68f90b5853a8d609e12f612573ec3d83c774` | `palomar/crossing_lemma/comparator.json` | [ ] Ready |
| **11** | **De Bruijn–Erdős Theorem on Incidence Geometry** | — | `abee7782a2f1ded1879358bd92c2c19df9d4383c` | `palomar/de_bruijn_erdos/comparator.json` | [ ] Ready |
| **12** | **Ore's and Dirac's Theorems on Hamiltonian Cycles** | — | `75cdaeeb860b3e71eb178e089dccebf24827e47f` | `palomar/ore_dirac_hamiltonian/comparator.json` | [ ] Ready |
| **13** | **Schur's Theorem on Sum-Free Partitions** | — | `b76dbcebd6d2a75354b3659a2ceecb2afe9fee5b` | `palomar/schurs_theorem/comparator.json` | [ ] Ready |
| **14** | **Dilworth's & Mirsky's Poset Theorems** | — | `b233f680f315facec4f8ee40fee10731c7fa8576` | `palomar/dilworth_mirsky/comparator.json` | [ ] Ready |
| | **Tier 3: Modern Extremal & Algebraic Methods** | | | | |
| **15** | **Kneser's Conjecture / Lovász's Bound (1978)** | — | `107768199deeb36c93fcd4cfadcc016aa05284eb` | `palomar/kneser_lovasz/comparator.json` | [ ] Ready |
| **16** | **Frankl–Wilson Theorem (Restricted Intersections)** | — | `5e88fb9300644f0ac6f94b01be0918d5ec2bd3f5` | `palomar/frankl_wilson/comparator.json` | [ ] Ready |
| **17** | **Szemerédi–Trotter Point-Line Incidences** | — | `6465868769dad1f7be8838a615703fac57180529` | `palomar/szemeredi_trotter/comparator.json` | [ ] Ready |
| **18** | **Spencer–Szemerédi–Trotter Erdős Unit Distances** | — | `bc7089518560b675276607d8652b43a5786362f3` | `palomar/erdos_unit_distances/comparator.json` | [ ] Ready |
| **19** | **Lovász's Colorful Helly Theorem (Bárány 1982)** | — | `bc5498cd232fbb4fee18e64a4f956dde5620bfb5` | `palomar/colorful_helly/comparator.json` | [ ] Ready |
| **20** | **Tutte's 1-Factor Theorem for Simple Graphs** | — | `8289c002351c860f385ce95fb5334501263687c9` | `palomar/tutte_one_factor/comparator.json` | [ ] Ready |
| **21** | **Elekes's Sum-Product Inequality** | — | `321932614f93fb0e0a30b55365296e383362ff52` | `palomar/elekes_sum_product/comparator.json` | [ ] Ready |
| **22** | **Cauchy's Arm Lemma & Convex Rigidity** | — | `7b4fd1ea4b01c33c4069a7ab42b02a26ed28a8fc` | `palomar/cauchy_arm_lemma/comparator.json` | [ ] Ready |
| **23** | **Tverberg's Theorem (1D & r ≤ 2)** | — | `6cdf6108a81a5d06de0961d02479099e5afb5c0f` | `palomar/tverbergs_theorem/comparator.json` | [ ] Ready |
| **24** | **Tucker's Combinatorial Lemma** | — | `9e9a2e7b29e4e00abc6732df68dafc89fbe66e00` | `palomar/tuckers_lemma/comparator.json` | [ ] Ready |
| **25** | **3D Sperner's Lemma (Tetrahedral Parity)** | — | `b447644cd64b67d64db7350726448e51adeff054` | `palomar/sperner_3d/comparator.json` | [ ] Ready |
| **26** | **Beck's Theorem on Incidence Geometry** | — | `5dff3137da6ad9202c857317cb9237c5067f2c68` | `palomar/becks_theorem/comparator.json` | [ ] Ready |
| **27** | **Friendship Windmill Structure Theorem** | — | `bf650580a5732aa6237613c2073c002f585234f0` | `palomar/friendship_windmill/comparator.json` | [ ] Ready |