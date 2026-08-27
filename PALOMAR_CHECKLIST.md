# Palomar Submission Master Priority Queue: Repo 1

All packages have completed rigorous pre-flight audits matching Palomar mechanical and AI editorial review standards.
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
| **13** | **Hall's Marriage Theorem (Matching SDRs)** | `4aed8276b644003f18386038594b70de666938c2` | [PALOMAR-2026-08-27-000012](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-27-000012) | [x] **LIVE** |
| **14** | **The Friendship Theorem (Unique Common Neighbors)** | `f60794e58faf3eb7032a78f7e756538cb6513da5` | [PALOMAR-2026-08-26-000011](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-26-000011) | [x] **LIVE** |
| **15** | **The Sylvester–Gallai Theorem (Ordinary Lines)** | `969b3d6d3e7381c9ec3003506cc7748fc0b6ba00` | [PALOMAR-2026-08-26-000013](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-26-000013) | [x] **LIVE** |
| **8** | **General n-Dimensional Sperner's Lemma** | `d14072a07f6c5a4dbca1428c7d013828d7c1a9da` | [PALOMAR-2026-08-27-000014](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-27-000014) | [x] **LIVE** |

---

## 🚀 Priority Submission Queue (Audited Unsubmitted Theorems)

| Priority # | Theorem / Package Title | Wiedijk # | Dedicated Commit SHA to Enter | Comparator Path | Status |
| :---: | :--- | :---: | :--- | :--- | :---: |
| | **Tier 1: Crown Jewels** | | | | |
| **1** | **Euler's Polyhedron Formula (V - E + F = 2)** | #13 | `213555c7fe3f85be051a784fbbb62305276d9c95` | `palomar/euler_polyhedron/comparator.json` | [ ] In Development |
| **3** | **Sperner's Lemma in 1D, 2D, and 3D** | #57 | — | `palomar/sperners_lemma/comparator.json` | [-] **Unsubmittable** (Superseded by live General n-D Sperner PALOMAR-2026-08-27-000014) |
| **4** | **Descartes's Rule of Signs** | #73 | `f4d767db9d42f0ed5652ecb81ded9689914dcd95` | `palomar/descartes_rule_of_signs/comparator.json` | [ ] Ready |
| **5** | **Radon's Lemma & Helly's Theorem** | #99 | `8640fa71ac7d050e04a5653c8537a268abb7e7f0` | `palomar/radon_helly/comparator.json` | [ ] Ready |
| **6** | **Pick's Theorem on Lattice Polygons** | #92 | `cac4bcf75095fde63d5cd10620c12ca663e7c0bf` | `palomar/picks_theorem/comparator.json` | [ ] Flagged for Geometry Refactor (manufactured triangulation) |
| | **Tier 2: Celebrated Combinatorics** | | | | |
| **8** | **Chvátal's Art Gallery Theorem (Fisk's 3-Coloring)** | — | `741ef84e35db054d7d903b8975467f62f334e684` | `palomar/art_gallery_theorem/comparator.json` | [ ] Ready |
| **9** | **Erdős–Szekeres Convex Polygon (Happy Ending 1935)** | — | `81f459c3cc35e066a5113e85b47d80fdba046b97` | `palomar/erdos_szekeres_convex/comparator.json` | [ ] Ready |
| **10** | **The Crossing Lemma (Ajtai et al. / Leighton 1982)** | — | `3fcfccd21e552d1641259f499fd40f4ae31e3a82` | `palomar/crossing_lemma/comparator.json` | [ ] Ready |
| **11** | **De Bruijn–Erdős Theorem on Incidence Geometry** | — | `9a62da97ff7d0ff237fd1ac8ff51737cf0463489` | `palomar/de_bruijn_erdos/comparator.json` | [ ] Ready |
| **12** | **Ore's and Dirac's Theorems on Hamiltonian Cycles** | — | `7c1b919f8017a0cfef4bd07c0df8a3853aea587c` | `palomar/ore_dirac_hamiltonian/comparator.json` | [ ] Ready |
| **13** | **Schur's Theorem on Sum-Free Partitions** | — | `a08b3b872d508d9adda0854e1e3baf73eefcde9c` | `palomar/schurs_theorem/comparator.json` | [ ] Ready |
| **14** | **Dilworth's & Mirsky's Poset Theorems** | — | `a2b95440872a366305d49f984d6bc9968ce5bd35` | `palomar/dilworth_mirsky/comparator.json` | [ ] Ready |
| | **Tier 3: Modern Extremal & Algebraic Methods** | | | | |
| **15** | **Kneser's Conjecture / Lovász's Bound (1978)** | — | `874272fd11bb1514ae15cb38ea6efe0a0963b2a1` | `palomar/kneser_lovasz/comparator.json` | [ ] Ready |
| **16** | **Frankl–Wilson Theorem (Restricted Intersections)** | — | `9790013fdb7353974e9bb47631171f61921d1c52` | `palomar/frankl_wilson/comparator.json` | [ ] Ready |
| **17** | **Szemerédi–Trotter Point-Line Incidences** | — | `ba3aea3b9f60bbbec74d239aeafedfa79dc92811` | `palomar/szemeredi_trotter/comparator.json` | [ ] Ready |
| **18** | **Spencer–Szemerédi–Trotter Erdős Unit Distances** | — | `17f17ac808b093912d04f832560278ef3a65e70b` | `palomar/erdos_unit_distances/comparator.json` | [ ] Ready |
| **19** | **Lovász's Colorful Helly Theorem (Bárány 1982)** | — | `b91a873395573a3544b16f331e715ad072f91ec9` | `palomar/colorful_helly/comparator.json` | [ ] Ready |
| **20** | **Tutte's 1-Factor Theorem for Simple Graphs** | — | `e426f5f98c1a1b0d776253616ef467e97e432bc6` | `palomar/tutte_one_factor/comparator.json` | [ ] Ready |
| **21** | **Elekes's Sum-Product Inequality** | — | `e8088ea4b6f71dbb3c5d7686e6b17f1cbe25d59e` | `palomar/elekes_sum_product/comparator.json` | [ ] Ready |
| **22** | **Cauchy's Arm Lemma & Convex Rigidity** | — | `4a89edf7f294d5887feb14a7bc0d1785b8529cd4` | `palomar/cauchy_arm_lemma/comparator.json` | [ ] Ready |
| **23** | **Tverberg's Theorem (1D & r ≤ 2)** | — | `ff3e3f62adc9955b3e52b47170185b1bdc5d6d2a` | `palomar/tverbergs_theorem/comparator.json` | [ ] Ready |
| **24** | **Tucker's Combinatorial Lemma** | — | `07d4f2fd09bf0b2122ad51c326bcfe268e1578b4` | `palomar/tuckers_lemma/comparator.json` | [ ] Ready |
| **25** | **3D Sperner's Lemma (Tetrahedral Parity)** | — | `48efc1a86911cdcc0a3678894f0f86fcb2bf8d87` | `palomar/sperner_3d/comparator.json` | [ ] Ready |
| **26** | **Beck's Theorem on Incidence Geometry** | — | `798fa332e18584c863a862b22935392d5f1cb3f3` | `palomar/becks_theorem/comparator.json` | [ ] Ready |
| **27** | **Friendship Windmill Structure Theorem** | — | `dbde6effd08ff1530828428f2b45c0b4dc58aeb4` | `palomar/friendship_windmill/comparator.json` | [ ] Ready |
