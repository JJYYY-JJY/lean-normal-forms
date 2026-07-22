# Citation audit for the v1.2.2 manuscript set

Audit baseline: repository commit `04caf3e37d639a9d561222c7374ffb69d7dd82b8`
(2026-07-21).  The line numbers below refer to that baseline.  Scope comprises
the seven manuscripts and public documentation that assigns an algorithm or
software component to another work.  License, download, dependency-provenance,
release-note, and benchmark-data URLs are intentionally out of scope.

`VERIFIED` means that the cited primary source, official documentation, or
fixed-commit source was inspected at the locator shown.  `BACKLOG` means that
the citation must not yet be used to support the stated claim: full text or a
more precise locator still has to be checked.  A bibliographic record alone is
not claim evidence.

## Release-gate summary

- The baseline contains 22 citation commands.  Lean/mathlib platform papers
  are suitable only for one environment citation per manuscript; they do not
  establish Lean 4.32.0, a mathlib API, an algorithm, correctness, or novelty.
- The core software citation must move to an artifact-availability/version
  sentence.  It cannot support the mathematical contribution or correctness.
- The Kannan--Bachem, LLL, Bird, and FLINT claims below have page-, equation-,
  or fixed-source evidence.  The detailed DKT schedule remains `BACKLOG`; the
  release text therefore makes only the high-level attribution supported by
  the publisher record and expressly disclaims a line-by-line reconstruction.
- Kannan--Bachem's paper uses a column-HNF convention.  Every row-HNF use in
  this repository must state the transpose/orientation adaptation; the original
  schedule must not be described as literally identical.
- `HexLLL` and `HexLLLMathlib` are actual pinned dependencies of the LLL
  development and must be credited at their Lake-resolved commits.
- The unused Cohen (1993) record in the former modular-HNF bibliography is
  deleted; Cohen remains canonical only for the core HNF claim at Algorithm
  2.4.5, pp. 68--69.

## Existing citation sites

### Core manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/sections/introduction.tex:10-12` (`deMouraUllrich2021Lean4`) | The project is implemented in Lean 4. | versioned software environment | de Moura--Ullrich, CADE 2021, pp. 625--635, describes Lean 4 as theorem prover and programming language. | **KEEP**, once in the environment paragraph; do not use it to establish version 4.32.0. | [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | VERIFIED |
| `paper/sections/introduction.tex:10-12` (`mathlib2020`) | The project is built on mathlib. | software environment | mathlib Community, CPP 2020, pp. 367--381, is the platform overview. | **KEEP**, once; exact APIs require commit-pinned source instead. | [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824) | VERIFIED |
| `paper/sections/introduction.tex:10-12` (`ji2026normalforms`) | Version 1.2.2 of the accompanying artifact fixes five public interfaces. | artifact availability | The canonical record names the exact `v1.2.2` release URL and is used only for versioned availability. | **MOVE** completed; it no longer supports the mathematical contribution or correctness. | [v1.2.2 release](https://github.com/JJYYY-JJY/lean-normal-forms/releases/tag/v1.2.2) | VERIFIED |
| `paper/sections/background.tex:42-44` (`baanen2025instance`) | `CanonicalMod` follows a lightweight instance-refinement style common in mathlib. | software-design precedent | Baanen surveys mathlib's instance-parameter/typeclass patterns, but the current wording does not identify a specific design pattern or section. | **DELETE** the vague attribution. **RESOLVED:** the release candidate removes the citation and claim. | [doi:10.1007/s10817-024-09712-7](https://doi.org/10.1007/s10817-024-09712-7) | VERIFIED |
| `paper/sections/background.tex:85-86` (`dummitfoote2004`) | Textbooks give an all-rows-at-once HNF definition. | mathematical definition | No HNF chapter/page was identified. | **DELETE** completed; neither the claim nor record remains in the release candidate. | Dummit--Foote, *Abstract Algebra*, 3rd ed. | VERIFIED |
| `paper/sections/background.tex:85-86` (`cohen1993`) | A textbook HNF specification is less recursive than this Lean predicate. | mathematical definition / algorithm | Algorithm 2.4.5, pp. 68--69, gives the extended-gcd column-operation schedule and final reductions. | **REPLACE** the broad citation with pp. 68--69 and state the row/column transpose. **RESOLVED** in the release candidate. | [doi:10.1007/978-3-662-02945-9](https://doi.org/10.1007/978-3-662-02945-9) | VERIFIED |
| `paper/sections/introduction.tex:69-72` (`divasonThiemann2022snf`) | Isabelle/HOL has a formalized, executable SNF algorithm, generic soundness, and uniqueness. | prior formalization | Abstract and §§4--6; the article states formal soundness for parameterized algorithms, uniqueness, arbitrary matrices, and certification; pp. 1065--1095. | **KEEP**, but split the comparison so this source supports only the Isabelle claims. | [doi:10.1007/s10817-022-09631-5](https://doi.org/10.1007/s10817-022-09631-5) | VERIFIED |
| `paper/sections/introduction.tex:69-72` (`cano2016coq`) | Coq has formalized linear algebra and Smith normal form over elementary-divisor rings. | prior formalization | Abstract and §§4--5 describe verified Smith algorithms over Euclidean domains and constructive PIDs and applications to module classification. | **KEEP**, adjacent only to the Coq claim. | [doi:10.2168/LMCS-12(2:7)2016](https://doi.org/10.2168/LMCS-12(2:7)2016) | VERIFIED |

### Rational-canonical manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/rational-canonical/sections/introduction.tex:28` (`demoura2021lean4`) | The application is implemented in Lean 4. | software environment | CADE 2021, pp. 625--635. | **KEEP** once; canonicalize the key and metadata. | [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | VERIFIED |
| `paper/rational-canonical/sections/introduction.tex:29` (`mathlib2020`) | The application uses mathlib. | software environment | CPP 2020, pp. 367--381. | **KEEP** once; do not use for `Matrix.charmatrix` or `Module.AEval'`. | [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824) | VERIFIED |

### Homology manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/homology/sections/introduction.tex:28` (`demoura2021lean4`) | The application is implemented in Lean 4. | software environment | CADE 2021, pp. 625--635. | **KEEP** once; canonicalize the key and metadata. | [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | VERIFIED |
| `paper/homology/sections/introduction.tex:29` (`mathlib2020`) | The application uses mathlib. | software environment | CPP 2020, pp. 367--381. | **KEEP** once; exact categorical-homology behavior requires commit-pinned source. | [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824) | VERIFIED |

### Bit-cost manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/bit-cost/main.tex:61-64` (`knuth1997seminumerical`) | The reference multiplication is classical multiple-precision shift-and-add. | arithmetic model | Knuth §4.3.1 defines the classical multiple-precision arithmetic algorithms. | **MOVE** completed; the citation is now local to the multiplication model and does not support matrix complexity. | [Knuth's official TAOCP page](https://www-cs-faculty.stanford.edu/~knuth/taocp.html) | VERIFIED |
| `paper/bit-cost/main.tex:61-64` (`brent2010modern`) | Multiplication, division, and gcd costs depend on operand length. | arithmetic model | Chapter 1, “Integer arithmetic,” pp. 1--46; contents locate multiplication §1.3, division §1.4, gcd/extended gcd §1.6 (pp. 29--36). | **MOVE** to the concrete arithmetic-model sections (`main.tex:138-228`) and limit it to those primitives. | [doi:10.1017/CBO9780511921698](https://doi.org/10.1017/CBO9780511921698) | VERIFIED |
| `paper/bit-cost/main.tex:247-250` (`demoura2021lean4`) | The code uses Lean/mathlib 4.32.0. | versioned software/API | The 2021 paper cannot establish a 2026 release or mathlib revision.  Lean tag `v4.32.0` resolves to `8c9756b...`; Lake pins mathlib `81a5d257...`. | **REPLACE** with the Lean v4.32.0 release/tag and Lake-pinned mathlib commit; retain the platform paper only in an environment introduction if desired. | [Lean 4.32.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/); [mathlib fixed commit](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997) | VERIFIED |
| `paper/bit-cost/main.tex:313-318` (`cohen1996hnf`) | Fast normal-form algorithms may use modular reconstruction or lattice reduction. | matrix-normal-form algorithm/complexity | The Cohen article did not verify the bundled claim. | **REPLACE** completed: the release text now gives separate Kannan--Bachem and DKT claims with their primary papers; the Cohen record is deleted. | [Kannan--Bachem](https://doi.org/10.1137/0208040); [DKT](https://doi.org/10.1287/moor.12.1.50) | VERIFIED |

### Kannan--Bachem manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/kannan-bachem/main.tex:61-65` (`kannan1979polynomial`) | Kannan--Bachem give the first polynomial HNF/SNF algorithms with polynomially bounded intermediate binary length. | original algorithm / complexity | Abstract, pp. 499--500; HNF Algorithm and Theorem 2, pp. 500--504; SNF Algorithm and Theorems 4--5, p. 505. | **KEEP**, and repeat locally at the algorithm and bound claims below. | [doi:10.1137/0208040](https://doi.org/10.1137/0208040) | VERIFIED |
| `paper/kannan-bachem/main.tex:73-76` (`demoura2021lean4`, `mathlib2020`) | The development is implemented in Lean 4 and mathlib. | software environment | CADE 2021, pp. 625--635; CPP 2020, pp. 367--381. | **KEEP** once; canonicalize both records. | [Lean 4 paper](https://doi.org/10.1007/978-3-030-79876-5_37); [mathlib paper](https://doi.org/10.1145/3372885.3373824) | VERIFIED |
| `paper/kannan-bachem/main.tex:171-189` (`bird2011determinants`) | Preparation uses Bird's division-free determinant recurrence. | original algorithm | Bird defines `mu(X)`, `F_A(X) = mu(X) A`, the `n-1` iteration, final sign, and determinant theorem on p. 1072; equation (1) and its proof occupy pp. 1072--1073.  These match `matrixStep`, `matrixIterate`, and `matrixBirdDet`. | **KEEP** with the page locator. **RESOLVED** after inspection of the article PDF. | [doi:10.1016/j.ipl.2011.08.006](https://doi.org/10.1016/j.ipl.2011.08.006) | VERIFIED |
| `paper/kannan-bachem/main.tex:260-265` (`brent2010modern`) | The scalar layer distinguishes algebraic operation count from bit cost and uses schoolbook arithmetic. | arithmetic model | Chapter 1, especially multiplication, division, and extended-gcd sections. | **KEEP/MOVE** next to the exact primitive definitions; it does not support matrix-level or certificate-composition bounds. | [doi:10.1017/CBO9780511921698](https://doi.org/10.1017/CBO9780511921698) | VERIFIED |
| `paper/kannan-bachem/main.tex:432-436` (`divason2022snf`) | SNF correctness has been formalized in other proof assistants. | prior formalization | Divasón--Thiemann abstract and §§4--6, pp. 1065--1095. | **KEEP**, but name Isabelle/HOL and state the actual overlap instead of a plural generic claim. | [doi:10.1007/s10817-022-09631-5](https://doi.org/10.1007/s10817-022-09631-5) | VERIFIED |

### Modular-HNF manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/modular-hnf/main.tex:67-71` (`domich1987hnf`) | DKT introduced an HNF method using modulo-determinant arithmetic. | original algorithm | Publisher abstract; *Mathematics of Operations Research* 12(1), pp. 50--59, states modulo-determinant computation and polynomial time. | **KEEP** for high-level provenance.  Do not let this citation carry the exact transition schedule without the detailed locator below. | [doi:10.1287/moor.12.1.50](https://doi.org/10.1287/moor.12.1.50) | VERIFIED |
| `paper/modular-hnf/main.tex:67-71` (`flint2026fmpzmat`) | FLINT gives the same DKT attribution. | versioned software/API | FLINT 3.6.0 source docs lines 1295--1314 describe the two modular-HNF APIs and attribute `fmpz_mat_hnf_modular` to DKT. | **MOVE** to the actual API/precondition comparison; software docs are not the historical algorithm source. | [FLINT 3.6.0 fixed source](https://github.com/flintlib/flint/blob/8d5454b96761fafe4d5a9da76a369a602f500f49/doc/source/fmpz_mat.rst#L1295-L1314) | VERIFIED |
| `paper/modular-hnf/main.tex:101-104` (`demoura2021lean4`, `mathlib2020`) | The implementation is in Lean/mathlib. | software environment | CADE 2021, pp. 625--635; CPP 2020, pp. 367--381. | **KEEP** once; canonicalize both records. | [Lean 4 paper](https://doi.org/10.1007/978-3-030-79876-5_37); [mathlib paper](https://doi.org/10.1145/3372885.3373824) | VERIFIED |
| `paper/modular-hnf/main.tex:285-290` (`brent2010modern`) | The cost layer distinguishes arithmetic operations and bit complexity. | arithmetic model | Chapter 1, pp. 1--46. | **MOVE** to the exact multiplication/division/XGCD model; it cannot support the modular-matrix complexity theorem. | [doi:10.1017/CBO9780511921698](https://doi.org/10.1017/CBO9780511921698) | VERIFIED |

### LLL manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/lll/main.tex:59-60` (`lll1982`) | LLL is a central lattice algorithm and preprocessing step. | original algorithm | §1 gives the reducedness conditions, algorithm, termination argument, and complexity; journal pp. 515--534. | **KEEP**, and add local citations at the predicate and potential claims below. | [doi:10.1007/BF01457454](https://doi.org/10.1007/BF01457454) | VERIFIED |
| `paper/lll/main.tex:59-60` (`cohen1993`) | LLL is used as a preprocessing step for exact matrix algorithms. | textbook application | No precise application page was inspected. | **DELETE** completed; the release text attributes only the original factoring algorithm and verified Isabelle formalization. | [LLL paper](https://doi.org/10.1007/BF01457454); [Isabelle formalization](https://doi.org/10.1007/s10817-020-09552-1) | VERIFIED |
| `paper/lll/main.tex:72-74` (`demoura2021lean4`, `mathlib2020`) | Lean 4 and mathlib supply exact matrix theory. | software environment | The platform papers describe Lean and mathlib, not the particular matrix APIs. | **KEEP** once for environment; cite fixed-commit sources for concrete APIs. | [Lean 4 paper](https://doi.org/10.1007/978-3-030-79876-5_37); [mathlib paper](https://doi.org/10.1145/3372885.3373824) | VERIFIED |

## Required added or moved citation sites

These rows are part of the v1.2.2 gate even though no `\cite...` command exists
at the baseline location.

### Core manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/sections/algorithm.tex:21-121` | The three-stage HNF elimination is an established HNF algorithm, with local Bézout clearing and top-row reduction. | original algorithm | Cohen Algorithm 2.4.5, pp. 68--69, performs extended-gcd column clearing and final quotient reductions. | **ADD** locally and state the row-oriented transpose. **RESOLVED** in the release candidate. | [Cohen book](https://doi.org/10.1007/978-3-662-02945-9) | VERIFIED |
| `paper/sections/intrinsic_smith.tex:27-61` | Determinantal ideals recover rank and Smith factors; the project proves their certificate invariance. | mathematical theorem | Newman p. 81 states the determinantal-divisor/invariant-factor relation; the certificate invariance is a local Lean theorem. | **ADD** completed next to the classical relation, without using software as mathematical evidence. | [doi:10.6028/jres.075B.019](https://doi.org/10.6028/jres.075B.019) | VERIFIED |
| `paper/sections/intrinsic_smith.tex:63-83` | The project compares its canonical Smith data with mathlib's PID Smith witnesses. | versioned API/source | `Mathlib/LinearAlgebra/FreeModule/PID.lean` documents and defines `Submodule.smithNormalForm` and related witnesses, especially lines 482--637. | **ADD** a fixed-commit source permalink, not `mathlib2020`. | [mathlib PID source at `81a5d257`](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/LinearAlgebra/FreeModule/PID.lean#L482-L637) | VERIFIED |
| `paper/sections/intrinsic_smith.tex:114-118` | The presentation layer uses the minors-of-a-presentation convention for Fitting ideals. | mathematical definition | Stacks Project Definition 15.8.3 (Tag 07Z6) fixes the convention and index. | **ADD** completed at the convention sentence; project-specific Smith consequences remain backed by Lean proofs. | [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6) | VERIFIED |
| `paper/sections/certificates.tex:66-83` | `decide_cbv` reduces a decidable proposition by call-by-value normalization without trusting generated native code. | versioned Lean behavior | Lean 4.32 reference, Tactic Reference §14.5.19.1, describes the two-step reduction, terminal behavior, standard axioms, and contrast with `native_decide`. | **ADD** official version/release documentation or source fixed to v4.32.0. | [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#decide-cbv) and [v4.32.0 release](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/) | VERIFIED |
| `paper/sections/introduction.tex:69-72` | Recent Lean work covers Smith normal form and rational canonical form through a general decomposition framework, but does not give canonical-associate uniqueness or an executable Smith trajectory. | prior formalization / overlap boundary | Ma--Wang--Wen v1, §5.4, pp. 22--23 and limitations pp. 27--28; it explicitly limits the current Smith statement and describes framework-level RCF/Smith instances. | **ADD**, with the boundary stated neutrally; do not infer features from the title/abstract. | [arXiv:2607.05874v1](https://arxiv.org/html/2607.05874v1) | VERIFIED |

### Rational-canonical manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/rational-canonical/sections/introduction.tex:3-17` | Invariant factors of `XI-A` determine the rational canonical form and companion-block decomposition. | mathematical classification theorem | MacDuffee, Chapter VI, pp. 112--136, develops the rational canonical form through invariant factors and companion matrices. | **ADD** completed beside the classification statement. | [doi:10.5948/UPO9781614440079.007](https://doi.org/10.5948/UPO9781614440079.007) | VERIFIED |
| `paper/rational-canonical/sections/presentation.tex:11-14` | mathlib's `Matrix.charmatrix A` is `X I - C(A)` with the stated entries. | versioned API/source | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, lines 49--63, defines `charmatrix` and proves diagonal/off-diagonal formulas. | **ADD** fixed-commit source. | [mathlib source at `81a5d257`](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L49-L63) | VERIFIED |
| `paper/rational-canonical/sections/decomposition.tex:3-4,38-40` | `Module.AEval' φ` gives the polynomial-module action with `X` acting by `φ`. | versioned API/source | `Mathlib/Algebra/Polynomial/Module/AEval.lean`, module docs lines 18--23 and declaration docs lines 183--195. | **ADD** fixed-commit source. | [mathlib source at `81a5d257`](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Polynomial/Module/AEval.lean#L18-L23) | VERIFIED |
| `paper/rational-canonical/sections/introduction.tex:24-32` | The overlap with Ma--Wang--Wen is at framework-level RCF existence/bridge data, while this manuscript claims executable Smith-derived factors and explicit companion similarity. | prior formalization / overlap boundary | Ma--Wang--Wen v1 §5.4, pp. 22--23; artifact environment Lean 4.25/mathlib `0a20708` and stated noncomputable instances delimit direct implementation comparison. | **ADD** a calibrated comparison. | [arXiv:2607.05874v1](https://arxiv.org/html/2607.05874v1) | VERIFIED |

### Homology manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/homology/sections/introduction.tex:3-19`; `decomposition.tex:15-25` | SNF computes homology of a finite free chain complex, including free rank and torsion cyclic factors. | mathematical theorem / algorithm | Kaczynski--Mischaikow--Mrozek, Chapter 3, pp. 93--141, gives the Smith-normal-form computation of homology. | **ADD** completed beside the computation and decomposition. | [doi:10.1007/b97315](https://doi.org/10.1007/b97315) | VERIFIED |
| `paper/homology/sections/simplicial.tex:15-33` | Normalized simplicial chains use nondegenerate simplices with alternating face boundary and compute the same homology. | mathematical theorem | Weibel Definition 8.3.6, Lemma 8.3.7, and Theorem 8.3.8, pp. 265--266, state the normalized complex and splitting. | **ADD** completed at the normalized-chain and comparison claims. | [doi:10.1017/CBO9781139644136.009](https://doi.org/10.1017/CBO9781139644136.009) | VERIFIED |
| `paper/homology/sections/mathlib-comparison.tex:3-55` | mathlib provides the categorical homology, normalized-chain, and normalized-Moore APIs used for comparison. | versioned API/source | The release candidate cites the exact imported modules at commit `81a5d257`, including the normalized-chain lines 16--131 and normalized-Moore lines 12--136. | **ADD** completed with separate fixed-source records rather than the overview paper. | [homology source](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean); [normalized chains](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Nondegenerate.lean#L16-L131); [normalized Moore](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/AlgebraicTopology/DoldKan/Normalized.lean#L12-L136) | VERIFIED |
| `paper/homology/sections/mathlib-comparison.tex:34-55` | mathlib's normalized chain complex is homotopy equivalent to the unnormalized complex and its normalized Moore construction is connected through the Dold--Kan normalization machinery. | versioned API/source | `SimplicialSet/Homology/Nondegenerate.lean` lines 16--22, 39--50, 84--131; `DoldKan/Normalized.lean` lines 12--24, 112--136. | **ADD** both fixed-commit source permalinks. | [nondegenerate normalized chains](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Nondegenerate.lean#L16-L131); [normalized Moore comparison](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/AlgebraicTopology/DoldKan/Normalized.lean#L12-L136) | VERIFIED |

### Bit-cost manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/bit-cost/main.tex:138-202` | The reference model is shift-and-add multiplication plus binary long division with signed Euclidean quotient/remainder conventions. | arithmetic algorithm/model | Knuth §4.3.1 supports the multiplication model; Brent--Zimmermann §1.4 supports division; Lean 4.32.0 `Init/Data/Int/DivMod/Basic.lean`, lines 43--118, fixes the signed convention. | **ADD/MOVE** completed with separate citations at each primitive. | [Modern Computer Arithmetic](https://doi.org/10.1017/CBO9780511921698); [Lean fixed source](https://github.com/leanprover/lean4/blob/v4.32.0/src/lean/Init/Data/Int/DivMod/Basic.lean#L43-L118) | VERIFIED |
| `paper/bit-cost/main.tex:204-228` | The reference XGCD follows the Euclidean recurrence and charges multiplication/addition by operand width. | arithmetic algorithm/model | Brent--Zimmermann §1.6, pp. 29--36, includes gcd and extended gcd. | **ADD** locally and restrict the citation to the recurrence/model, not this project's proved budgets. | [doi:10.1017/CBO9780511921698](https://doi.org/10.1017/CBO9780511921698) | VERIFIED |

### Kannan--Bachem manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/kannan-bachem/main.tex:141-152` | The principal-minor HNF schedule and polynomial operation bound follow Kannan--Bachem. | original algorithm / complexity | HNF Algorithm, pp. 500--501; Theorem 2, p. 504.  The source uses column operations/column-HNF. | **ADD** locally and state that this manuscript applies the transposed row-HNF orientation. | [doi:10.1137/0208040](https://doi.org/10.1137/0208040) | VERIFIED |
| `paper/kannan-bachem/main.tex:193-225` | Smith Steps 4--7 alternate HNF passes, repeat on uncleared pivot column, inject an offending column, and terminate by pivot decrease. | original algorithm | SNF Algorithm Steps 4--7 and Theorem 4, p. 505. | **ADD** locally; explicitly record all orientation/transposition changes. | [doi:10.1137/0208040](https://doi.org/10.1137/0208040) | VERIFIED |
| `paper/kannan-bachem/main.tex:239-288` | Operation counts and intermediate/multiplier coefficient lengths are polynomial. | complexity / coefficient bound | Abstract pp. 499--500; Theorems 2, 4, and 5, pp. 504--505. | **ADD** adjacent to the separate operation and coefficient claims; the paper does not support this project's exact constants without the Lean proofs. | [doi:10.1137/0208040](https://doi.org/10.1137/0208040) | VERIFIED |

### Modular-HNF manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/modular-hnf/main.tex:110-168` | The baseline bundled the exact transition order, centered reduction, determinant-modulus premise, and correctness contract as DKT. | original algorithm / theorem | The publisher-accessible primary record exposes only the abstract; a page-level algorithm/theorem match has not been checked. | **NARROW** completed: the release candidate claims only membership in DKT's high-level modulo-determinant class and expressly disclaims a line-by-line reconstruction. Detailed mapping remains post-release backlog. | [doi:10.1287/moor.12.1.50](https://doi.org/10.1287/moor.12.1.50) | VERIFIED |
| `paper/modular-hnf/main.tex:118-132` | FLINT's determinant-modulus and elementary-divisor modular-HNF entry points have distinct unchecked preconditions. | versioned API/software | FLINT 3.6.0 docs, `fmpz_mat.rst` lines 1295--1314. | **ADD/MOVE** the fixed-source citation here. | [FLINT 3.6.0 fixed source](https://github.com/flintlib/flint/blob/8d5454b96761fafe4d5a9da76a369a602f500f49/doc/source/fmpz_mat.rst#L1295-L1314) | VERIFIED |

### LLL manuscript

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `paper/lll/main.tex:90-110` | Reducedness uses `abs(mu_ij) <= 1/2` and the Lovász condition with `delta = 3/4`. | original definition | LLL §1, equations (1.4)--(1.5), journal pp. 517--518. | **ADD** adjacent to the displayed predicate. | [doi:10.1007/BF01457454](https://doi.org/10.1007/BF01457454) | VERIFIED |
| `paper/lll/main.tex:124-135` | Termination uses the classical product potential; swaps decrease it, while the executable uses a pinned fuel theorem. | mathematical algorithm plus versioned dependency | LLL equations (1.23)--(1.25), pp. 524--525, prove the classical potential descent. `HexLLL` and `HexLLLMathlib` define/prove the project-specific fuel at the pinned commits. | **ADD** the LLL paper for the classical argument and both fixed commits for the implemented fuel; keep the roles separate. | [LLL paper](https://doi.org/10.1007/BF01457454); [HexLLL](https://github.com/leanprover/hex-lll/tree/a73f188bbd7ea48c4a1bb1e6d608b4f131026512); [HexLLLMathlib](https://github.com/leanprover/hex-lll-mathlib/tree/c10d6681dee9a4f963c1035bcbe34fc3eb60a769) | VERIFIED |
| `paper/lll/main.tex:111-147` | Executable reducedness/checking and dense reduction are reused from `HexLLL`/`HexLLLMathlib`, while this project adds its trace/certificate layer. | software/API attribution | `HexLLL/Reduced.lean` lines 35--54 and `Native.lean` lines 452--560; `HexLLLMathlib/Reducer.lean` lines 1900--2116 and 2373--2410; `Checker.lean` lines 360--368. | **ADD** fixed-commit attribution and distinguish upstream code/proofs from local additions. | [HexLLL reducedness/native loop](https://github.com/leanprover/hex-lll/blob/a73f188bbd7ea48c4a1bb1e6d608b4f131026512/HexLLL/Reduced.lean#L35-L54); [HexLLLMathlib proof source](https://github.com/leanprover/hex-lll-mathlib/blob/c10d6681dee9a4f963c1035bcbe34fc3eb60a769/HexLLLMathlib/Reducer.lean#L1900-L2116) | VERIFIED |
| `paper/lll/main.tex:57-86` | Prior formalization has verified LLL soundness, polynomial running time, and certification in Isabelle/HOL. | prior formalization | Thiemann et al., JAR 64 (2020), pp. 827--856; author-institution abstract states implementation, soundness, polynomial running time, and external-result certification. | **ADD** to a short related-work sentence. | [doi:10.1007/s10817-020-09552-1](https://doi.org/10.1007/s10817-020-09552-1) | VERIFIED |

## Public documentation with algorithm attribution

These are documentation edits, not additional academic bibliography sites.  A
short DOI link or fixed-commit source link is sufficient, provided it is next to
the actual attribution.

| Manuscript/location | Claim | Role | Source evidence | Verdict | Primary source | Status |
|---|---|---|---|---|---|---|
| `docs/KANNAN_BACHEM_API.md:15-18,60-88` | Principal-minor HNF and Smith Steps 4--7 are Kannan--Bachem schedules. | algorithm attribution | HNF Algorithm pp. 500--501; SNF Algorithm Steps 4--7 p. 505. | **ADD** DOI link and a row/column-transpose note. | [doi:10.1137/0208040](https://doi.org/10.1137/0208040) | VERIFIED |
| `docs/KANNAN_BACHEM_API.md:155-167`; `artifact/kannan-bachem/README.md:10-12` | The determinant selector uses Bird's division-free recurrence. | algorithm attribution | Bird p. 1072 defines the exact matrix recurrence and endpoint; pp. 1072--1073 prove equation (1). | **ADD** DOI and page locator. **RESOLVED** in the release candidate. | [doi:10.1016/j.ipl.2011.08.006](https://doi.org/10.1016/j.ipl.2011.08.006) | VERIFIED |
| `docs/MODULAR_HNF_API.md:28-31`; `artifact/modular-hnf/README.md:3-6` | The value kernel belongs to the modulo-determinant HNF class introduced by DKT. | algorithm attribution | The publisher abstract verifies modulo-determinant HNF and polynomial time at the class level. | **NARROW/ADD** completed; the docs no longer claim that the exact local schedule or correctness contract was recovered from the article. | [doi:10.1287/moor.12.1.50](https://doi.org/10.1287/moor.12.1.50) | VERIFIED |
| `artifact/modular-hnf/README.md:55-57` | FLINT informed the transition order. | software/API attribution | FLINT docs identify DKT and API contracts but do not themselves prove that the repository transition order matches DKT. | **REPLACE** with a precise statement of which FLINT 3.6.0 API/source behavior was consulted, or delete the transition-order inference. | [FLINT 3.6.0 fixed source](https://github.com/flintlib/flint/blob/8d5454b96761fafe4d5a9da76a369a602f500f49/doc/source/fmpz_mat.rst#L1295-L1314) | VERIFIED |
| `docs/LLL_API.md:9-10,68-71,115-122`; `artifact/README.md:95-103` | The terminating reducer, predicate, and fuel theorem are source-pinned upstream components. | software/API attribution | Lake resolves `HexLLL` to `a73f188...` and `HexLLLMathlib` to `c10d668...`; exact source locators are recorded above. | **ADD** both fixed-commit links and name the upstream ownership. | [HexLLL fixed commit](https://github.com/leanprover/hex-lll/tree/a73f188bbd7ea48c4a1bb1e6d608b4f131026512); [HexLLLMathlib fixed commit](https://github.com/leanprover/hex-lll-mathlib/tree/c10d6681dee9a4f963c1035bcbe34fc3eb60a769) | VERIFIED |
| `artifact/README.md:77-104` | The profile names Kannan--Bachem, DKT, and LLL algorithms. | algorithm attribution | Primary-source evidence is recorded in the manuscript rows above. | **ADD** one compact source link per named profile; do not create bibliography entries for release metadata or dependency provenance. | Kannan--Bachem, DKT, and LLL DOI links above | VERIFIED |

## Canonical bibliography decisions

`paper/references.bib` should be the only project bibliography.  The six
submanuscripts should use `../references` (relative to their build directory as
appropriate), and their local `.bib` files should be removed after every key is
migrated.

| Canonical key | Required canonical metadata | Current duplicates/actions |
|---|---|---|
| `deMouraUllrich2021Lean4` | CADE 28, LNCS 12699, pp. 625--635, Springer, 2021, DOI `10.1007/978-3-030-79876-5_37` | Rename all `demoura2021lean4`; do not cite it for Lean 4.32.0. |
| `mathlib2020` | CPP 2020, pp. 367--381, ACM, DOI `10.1145/3372885.3373824` | Preserve corporate author braces; use only as platform overview. |
| `cohen1993` | Henri Cohen, GTM 138, Springer, 1993, DOI `10.1007/978-3-662-02945-9` | Merge `cohen1993course`; retain only if an exact chapter/page supports a claim. |
| `divasonThiemann2022snf` | JAR 66(4), pp. 1065--1095, DOI `10.1007/s10817-022-09631-5` | Rename `divason2022snf`; note the published correction DOI `10.1007/s10817-022-09636-0` when extracting exact corrected claims. |
| `brentZimmermann2010` | Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, CUP, 2010, DOI `10.1017/CBO9780511921698` | Replace all `brent2010modern`; add edition/ISBN only if consistently verified. |
| `cohen1996Dedekind` | *Mathematics of Computation* 65(216), pp. 1681--1699, DOI `10.1090/S0025-5718-96-00766-1` | Deleted: no release claim needs this article. |
| `maWangWen2026` | Wanli Ma, Zichen Wang, Zaiwen Wen, arXiv:2607.05874v1 [math.NA], 7 July 2026, DOI `10.48550/arXiv.2607.05874` | Added with v1 explicit; future arXiv versions may change the cited limitation text. |
| `hexLLL2026` / `hexLLLMathlib2026` | repository owner/author, title, year, exact commits `a73f188...` / `c10d668...`, stable source URLs | Add software records; use only for implementation/API/proof ownership. |

## Primary-source registry

| Work | Evidence safe to cite now | Primary source | Status |
|---|---|---|---|
| Lean 4 | Platform description: CADE 2021, pp. 625--635. Version 4.32.0: official release/tag `v4.32.0` (`8c9756b...`). | [paper](https://doi.org/10.1007/978-3-030-79876-5_37); [release](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/) | VERIFIED |
| mathlib | Platform overview: CPP 2020, pp. 367--381. Repository API behavior: fixed commit `81a5d257...`. | [paper](https://doi.org/10.1145/3372885.3373824); [source](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997) | VERIFIED |
| Cohen (1993) | HNF Algorithm 2.4.5 and its orientation, pp. 68--69. | [Springer book](https://doi.org/10.1007/978-3-662-02945-9) | VERIFIED |
| Divasón--Thiemann (2022) | Isabelle SNF algorithms, generic soundness, uniqueness, and certification; article §§4--6, pp. 1065--1095. | [Springer article](https://doi.org/10.1007/s10817-022-09631-5) | VERIFIED |
| Cano et al. (2016) | Coq linear algebra over elementary-divisor rings, verified Smith algorithms, module classification. | [LMCS article](https://doi.org/10.2168/LMCS-12(2:7)2016) | VERIFIED |
| Ma--Wang--Wen (2026) | Matrix-decomposition framework; Smith/RCF bridge instances and explicit current limitations, v1 §5.4 and pp. 27--28. | [arXiv v1 HTML](https://arxiv.org/html/2607.05874v1) | VERIFIED |
| Newman (1971) | Determinantal divisors and invariant factors, p. 81. | [NIST DOI](https://doi.org/10.6028/jres.075B.019) | VERIFIED |
| Stacks Project | Fitting ideals from minors of a presentation, Definition 15.8.3, Tag 07Z6. | [Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6) | VERIFIED |
| MacDuffee (1943) | Invariant-factor classification and companion-block rational canonical form, Chapter VI, pp. 112--136. | [MAA DOI](https://doi.org/10.5948/UPO9781614440079.007) | VERIFIED |
| Kaczynski--Mischaikow--Mrozek (2004) | Smith-normal-form computation of finite-chain-complex homology, Chapter 3, pp. 93--141. | [Springer DOI](https://doi.org/10.1007/b97315) | VERIFIED |
| Weibel (1994) | Normalized chains and the degenerate splitting, Definition 8.3.6, Lemma 8.3.7, and Theorem 8.3.8, pp. 265--266. | [Cambridge DOI](https://doi.org/10.1017/CBO9781139644136.009) | VERIFIED |
| Kannan--Bachem (1979) | HNF Algorithm/Theorem 2 pp. 500--504; SNF Steps 4--7/Theorems 4--5 p. 505; polynomial operation and coefficient-length claims. | [SIAM DOI](https://doi.org/10.1137/0208040) | VERIFIED |
| DKT (1987), high-level | Modulo-determinant HNF and polynomial-time claim, pp. 50--59, from the publisher abstract. | [INFORMS DOI](https://doi.org/10.1287/moor.12.1.50) | VERIFIED |
| DKT (1987), detailed mapping | Exact transition, invariant, premise, and theorem locators have not been checked against full text; no v1.2.2 claim relies on them. | [INFORMS DOI](https://doi.org/10.1287/moor.12.1.50) | BACKLOG |
| LLL (1982) | Reducedness (1.4)--(1.5), algorithm (1.15)--(1.22), termination (1.23)--(1.25), complexity Proposition (1.26), pp. 517--527. | [journal DOI](https://doi.org/10.1007/BF01457454); [CWI full text](https://ir.cwi.nl/pub/9304/9304D.pdf) | VERIFIED |
| Bird (2011) | Exact `mu`/`F_A` recurrence, endpoint theorem, and equation (1), pp. 1072--1073; complexity discussion, pp. 1072--1074. | [Elsevier DOI](https://doi.org/10.1016/j.ipl.2011.08.006) | VERIFIED |
| Brent--Zimmermann (2010) | Integer-arithmetic models, Chapter 1 pp. 1--46; multiplication, division, gcd, extended gcd. | [Cambridge DOI](https://doi.org/10.1017/CBO9780511921698) | VERIFIED |
| Knuth (1997) | Classical multiple-precision addition, multiplication, and division algorithms, §4.3.1. | [official TAOCP page](https://www-cs-faculty.stanford.edu/~knuth/taocp.html) | VERIFIED |
| Lean 4.32.0 APIs | Euclidean integer division/modulus: `Init/Data/Int/DivMod/Basic.lean` lines 43--118. `decide_cbv`: `Init/Tactics.lean` lines 2386--2401. | [division source](https://github.com/leanprover/lean4/blob/v4.32.0/src/lean/Init/Data/Int/DivMod/Basic.lean#L43-L118); [tactic source](https://github.com/leanprover/lean4/blob/v4.32.0/src/lean/Init/Tactics.lean#L2386-L2401) | VERIFIED |
| FLINT 3.6.0 | `fmpz_mat_hnf_modular` and `_eldiv` contracts and unchecked premises, source lines 1295--1314 at release commit `8d5454b...`. | [fixed source](https://github.com/flintlib/flint/blob/8d5454b96761fafe4d5a9da76a369a602f500f49/doc/source/fmpz_mat.rst#L1295-L1314) | VERIFIED |
| HexLLL | Reducedness, native loop, classical parameters, and fuel at Lake-pinned commit `a73f188...`. | [fixed source](https://github.com/leanprover/hex-lll/tree/a73f188bbd7ea48c4a1bb1e6d608b4f131026512) | VERIFIED |
| HexLLLMathlib | Fuel sufficiency, native correctness, and checker soundness at Lake-pinned commit `c10d668...`. | [fixed source](https://github.com/leanprover/hex-lll-mathlib/tree/c10d6681dee9a4f963c1035bcbe34fc3eb60a769) | VERIFIED |

## Explicit post-v1.2.2 backlog

The six side manuscripts do not need a full Related Work section for v1.2.2,
but the following items may not be represented as verified before they are
closed:

1. inspect the full DKT article and map each modular transition, premise,
   invariant, and correctness statement to an algorithm/lemma/theorem and page;
   v1.2.2 makes no detailed-reconstruction claim while this remains open;
2. in the post-release CPP branch, expand the core comparison set and audit each
   comparison-table cell against a paper theorem or fixed source rather than a
   title or abstract.

No `BACKLOG` row licenses a release manuscript to retain a false, vague, or
misplaced citation.  If the claim is necessary for v1.2.2, the backlog must be
closed; otherwise the claim or citation must be removed or narrowed.
