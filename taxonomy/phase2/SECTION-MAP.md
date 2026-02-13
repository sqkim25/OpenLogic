# SECTION-MAP — Phase 2 Master Mapping

## Batch 1 — BST (sets-functions-relations/)


### Chapter: sets

### sfr/set/bas — Extensionality
- **File**: content/sets-functions-relations/sets/basics.tex
- **Domain**: BST
- **Introduces**: PRIM-BST001, PRIM-BST002, PRIM-BST004
- **References**: 
- **OL Formal Items**: 
  - \begin{defn}[Extensionality] → PRIM-BST001 (Set identity criterion)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: 
- **OL Cross-refs**: 
- **Notes**: Introduces the primitive notion of set, membership (∈), and empty set (∅). Extensionality is the foundational principle for set equality. Also introduces set-builder notation {x | φ(x)}.

### sfr/set/sub — Subsets and Power Sets
- **File**: content/sets-functions-relations/sets/subsets.tex
- **Domain**: BST
- **Introduces**: PRIM-BST003, PRIM-BST015
- **References**: PRIM-BST001, PRIM-BST002, PRIM-BST004
- **OL Formal Items**: 
  - \begin{defn}[Subset] → PRIM-BST003
  - \begin{prop} (line 52) → OL-ONLY: stepping stone (extensionality ↔ mutual subsets)
  - \begin{defn}[forallxina] → OL-ONLY: pedagogical (bounded quantifier notation)
  - \begin{defn}[Power Set] → PRIM-BST015
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/set/bas
- **OL Cross-refs**: 
- **Notes**: Defines subset relation and power set. The proposition relating extensionality to mutual subsets is a key bridge lemma. Also introduces bounded quantifier notation (∀x∈A)φ.

### sfr/set/imp — Some Important Sets
- **File**: content/sets-functions-relations/sets/important-sets.tex
- **Domain**: BST
- **Introduces**: PRIM-BST012, PRIM-BST010, PRIM-BST011
- **References**: PRIM-BST003, PRIM-BST001
- **OL Formal Items**: 
  - No formal \begin{defn/thm} with labels, but introduces:
    - ℕ (natural numbers) → PRIM-BST012
    - ℤ (integers) → OL-ONLY: pedagogical
    - ℚ (rationals) → OL-ONLY: pedagogical
    - ℝ (reals) → OL-ONLY: pedagogical
    - A* (finite strings) → PRIM-BST010
    - A^ω (infinite sequences) → PRIM-BST011
- **Role**: DEFINE, DISCUSS
- **Compression Signal**: CORE-DEF, PEDAGOGICAL
- **Ped. Prerequisites**: sfr/set/bas, sfr/set/sub
- **OL Cross-refs**: sfr/arith/real/realline (conditional)
- **Notes**: Introduces standard mathematical sets. Natural numbers are primitive for induction/recursion. Finite/infinite sequences are primitives for syntax domains. ℤ, ℚ, ℝ are pedagogical context.

### sfr/set/uni — Unions and Intersections
- **File**: content/sets-functions-relations/sets/unions-and-intersections.tex
- **Domain**: BST
- **Introduces**: PRIM-BST005
- **References**: PRIM-BST001, PRIM-BST002, PRIM-BST003, PRIM-BST004
- **OL Formal Items**: 
  - \begin{defn}[Union] → PRIM-BST005 (∪)
  - \begin{defn}[Intersection] → PRIM-BST005 (∩)
  - \begin{defn} (line 109, general union ⋃A) → PRIM-BST005
  - \begin{defn} (line 120, general intersection ⋂A) → PRIM-BST005
  - \begin{defn}[Difference] → OL-ONLY: pedagogical (set difference, not in primitive list)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/set/bas, sfr/set/sub
- **OL Cross-refs**: sfr/set/bas (line 13)
- **Notes**: Defines binary and arbitrary union/intersection operations. Also introduces set difference (A∖B) and disjoint sets. Includes indexed unions/intersections.

### sfr/set/pai — Pairs, Tuples, Cartesian Products
- **File**: content/sets-functions-relations/sets/pairs-and-products.tex
- **Domain**: BST
- **Introduces**: PRIM-BST006, PRIM-BST007, PRIM-BST010
- **References**: PRIM-BST001, PRIM-BST004
- **OL Formal Items**: 
  - \begin{defn}[Ordered pair, wienerkuratowski] → PRIM-BST006
  - \begin{defn}[Cartesian product] → PRIM-BST007
  - \begin{prop}[cardnmprod] → OL-ONLY: stepping stone (|A×B| = |A|·|B|)
- **Role**: DEFINE, PROVE
- **Compression Signal**: CORE-DEF, STEPPING-STONE
- **Ped. Prerequisites**: sfr/set/bas, sfr/set/sub
- **OL Cross-refs**: 
- **Notes**: Wiener-Kuratowski definition ⟨a,b⟩ = {{a},{a,b}} reduces ordered pairs to sets. Defines n-tuples recursively. Cartesian product A×B and A^n. The cardinality proposition includes proof. Example of A* (words) connects to PRIM-BST010.

### sfr/set/rus — Russell's Paradox
- **File**: content/sets-functions-relations/sets/russells-paradox.tex
- **Domain**: BST
- **Introduces**: 
- **References**: PRIM-BST001, PRIM-BST002, PRIM-BST015
- **OL Formal Items**: 
  - \begin{thm}[Russell's Paradox, thm:russells-paradox] → OL-ONLY: GAP-CANDIDATE: Limitation of Size / Comprehension Restriction
- **Role**: DISCUSS, PROVE
- **Compression Signal**: PEDAGOGICAL, TANGENTIAL
- **Ped. Prerequisites**: sfr/set/bas, sfr/set/sub
- **OL Cross-refs**: cumul (part reference, conditional)
- **Notes**: Proves that R = {x | x ∉ x} cannot exist. Motivates need for axiomatic set theory. Largely pedagogical/cautionary. Could map to a metatheoretic principle about comprehension limits, but this is informal discussion rather than formal axiomatics. References future rigorous development in Part cumul.

### sfr/set/prf — Proofs about Sets
- **File**: content/sets-functions-relations/sets/proofs-about-sets.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST001 (Set), PRIM-BST003 (Subset), PRIM-BST005 (Union/Intersection)
- **OL Formal Items**:
  - \begin{prop}[Absorption] → OL-ONLY: pedagogical (X ∩ (X ∪ Y) = X — worked example of set proof)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sfr/set/bas, sfr/set/sub, sfr/set/uni
- **OL Cross-refs**: (none)
- **Notes**: INACTIVE — editorial note says "superseded by content/methods/proofs and removed from this chapter by default." Not imported in sets.tex chapter aggregator. Contains a detailed worked example of proving a set identity (absorption law) followed by compressed version. Purely pedagogical proof methodology.



### Chapter: functions

### sfr/fun/bas — Basics
- **File**: content/sets-functions-relations/functions/function-basics.tex
- **Domain**: BST
- **Introduces**: PRIM-BST009
- **References**: PRIM-BST001, PRIM-BST002, PRIM-BST006, PRIM-BST007
- **OL Formal Items**: 
  - \begin{defn}[Function] → PRIM-BST009 (defining occurrence: function f:A→B, domain, codomain, range)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: (first section in chapter)
- **OL Cross-refs**: (none in this file)
- **Notes**: Introduces function as primitive concept with domain, codomain, arguments, values, and range. Discusses extensionality principle for functions informally. Uses Cartesian product (PRIM-BST007) in examples (Nat × Nat).

---

### sfr/fun/kin — Kinds of Functions
- **File**: content/sets-functions-relations/functions/function-kinds.tex
- **Domain**: BST
- **Introduces**: DEF-BST002, DEF-BST001, DEF-BST003
- **References**: PRIM-BST009
- **OL Formal Items**:
  - \begin{defn}[surjective function] → DEF-BST002 (surjection: ∀y∈B ∃x∈A f(x)=y)
  - \begin{defn}[injective function] → DEF-BST001 (injection: each y has at most one x)
  - \begin{defn}[bijection] → DEF-BST003 (bijection: both injective and surjective)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/fun/bas
- **OL Cross-refs**: (none in this file)
- **Notes**: Three core function properties defined with diagrams. Notes that any function induces a surjection to its range.

---

### sfr/fun/rel — Functions as Relations
- **File**: content/sets-functions-relations/functions/functions-relations.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST009, PRIM-BST008, PRIM-BST006, PRIM-BST001, PRIM-BST003
- **OL Formal Items**:
  - \begin{defn}[Graph of a function] → OL-ONLY: pedagogical (identifies functions with relations)
  - \begin{prop}[prop:graph-function] → OL-ONLY: pedagogical (functional relations are graphs)
  - \begin{defn}[defn:funimage] → OL-ONLY: pedagogical (restriction, application/image)
- **Role**: DISCUSS, DEFINE (derived concepts)
- **Compression Signal**: PEDAGOGICAL, STEPPING-STONE
- **Ped. Prerequisites**: sfr/fun/bas
- **OL Cross-refs**: sfr/rel/ref (references spirit of identification), sfr/rel/ops (operations on relations), sfr/fun/inv, sfr/fun/cmp
- **Notes**: Bridges functions and relations (PRIM-BST008). Graph concept enables treating functions as sets of pairs. Defines restriction and image operations. References relation operations from earlier chapter.

---

### sfr/fun/inv — Inverses of Functions
- **File**: content/sets-functions-relations/functions/inverses.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST009, DEF-BST001, DEF-BST002, DEF-BST003
- **OL Formal Items**:
  - \begin{defn}[inverse] → OL-ONLY: pedagogical (inverse function g with f(g(y))=y and g(f(x))=x)
  - \begin{prop}[injective → left inverse] → OL-ONLY: pedagogical
  - \begin{prop}[surjective → right inverse] → OL-ONLY: pedagogical (requires Axiom of Choice)
  - \begin{prop}[prop:bijection-inverse] → OL-ONLY: pedagogical (bijection has unique inverse)
  - \begin{prop}[prop:left-right] → OL-ONLY: pedagogical (left inverse = right inverse)
  - \begin{prop}[prop:inverse-unique] → OL-ONLY: pedagogical (uniqueness of inverse)
- **Role**: DEFINE (derived concepts), PROVE
- **Compression Signal**: CORE-THM, STEPPING-STONE
- **Ped. Prerequisites**: sfr/fun/bas, sfr/fun/kin
- **OL Cross-refs**: sfr/fun/kin (references injective/surjective), sth/choice (Axiom of Choice mentioned in footnote)
- **Notes**: Key theorems connecting function properties to invertibility. Axiom of Choice mentioned for surjective right inverses. Three problems assigned as exercises.

---

### sfr/fun/cmp — Composition of Functions
- **File**: content/sets-functions-relations/functions/composition.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST009, DEF-BST001, DEF-BST002
- **OL Formal Items**:
  - \begin{defn}[Composition] → OL-ONLY: pedagogical (g∘f where (g∘f)(x) = g(f(x)))
- **Role**: DEFINE (derived operation), APPLY
- **Compression Signal**: CORE-DEF, STEPPING-STONE
- **Ped. Prerequisites**: sfr/fun/bas, sfr/fun/kin
- **OL Cross-refs**: sfr/fun/inv (references inverse section), sfr/rel/ops (analogue of relative product)
- **Notes**: Defines composition operation. Three problems show composition preserves injection, surjection, and that graph of composition is relative product of graphs. Connects to relation operations.

---

### sfr/fun/iso — Isomorphism
- **File**: content/sets-functions-relations/functions/isomorphic-functions.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST009, PRIM-BST008, DEF-BST003
- **OL Formal Items**:
  - \begin{defn}[Isomorphism] → OL-ONLY: GAP-CANDIDATE: structure-preserving bijection (isomorphism between relational structures U=⟨X,R⟩ and V=⟨Y,S⟩)
- **Role**: DEFINE (application concept)
- **Compression Signal**: PEDAGOGICAL, TANGENTIAL
- **Ped. Prerequisites**: sfr/fun/bas, sfr/fun/kin
- **OL Cross-refs**: (none in this file)
- **Notes**: Specialized concept combining bijection (DEF-BST003) with relation-preservation. Structure-preserving maps are important in logic/model theory but not primitive to basic set theory. Could be elevated if needed for model-theoretic applications.

---

### sfr/fun/par — Partial Functions
- **File**: content/sets-functions-relations/functions/partial-functions.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST009, PRIM-BST008
- **OL Formal Items**:
  - \begin{defn}[partial function] → OL-ONLY: GAP-CANDIDATE: partial function (f:A ⇀ B with defined/undefined distinction)
  - \begin{defn}[Graph of a partial function] → OL-ONLY: pedagogical (extension of function graph)
  - \begin{prop}[relation to partial function] → OL-ONLY: pedagogical (functional relations yield partial functions)
- **Role**: DEFINE (generalization), DISCUSS
- **Compression Signal**: PEDAGOGICAL, TANGENTIAL
- **Ped. Prerequisites**: sfr/fun/bas, sfr/fun/rel
- **OL Cross-refs**: (none in this file)
- **Notes**: Generalizes function concept by relaxing totality requirement. Important for computation (recursive functions) but not primitive to basic set theory. Domain of partial function is subset where defined. Distinguishes total vs partial functions.



### Chapter: relations

### sfr/rel/set — Relations as Sets
- **File**: content/sets-functions-relations/relations/relations-as-sets.tex
- **Domain**: BST
- **Introduces**: PRIM-BST008
- **References**: PRIM-BST006 (Ordered Pair), PRIM-BST007 (Cartesian Product), PRIM-BST012 (ℕ), PRIM-BST004 (∅)
- **OL Formal Items**: 
  - \begin{defn}[Binary relation] → PRIM-BST008 (defining occurrence)
  - \begin{ex}[relations] → OL-ONLY: pedagogical (examples of identity, less-than, greater-than relations)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: (references sfr/set/imp and sfr/set/pai from earlier chapters)
- **OL Cross-refs**: \olref[sfr][set][imp]{sec}, \olref[sfr][set][pai]{sec}
- **Notes**: Defines binary relation as subset of A². Introduces notation Rxy for ⟨x,y⟩∈R. Examples include identity relation Id(A), order relations (<, ≤, >, ≥), empty relation, universal relation. References ordered pairs and Cartesian products from prior sections.

### sfr/rel/ref — Philosophical Reflections
- **File**: content/sets-functions-relations/relations/reflections.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: PRIM-BST008, PRIM-BST006, PRIM-BST002
- **OL Formal Items**: (none - no formal definitions/theorems)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sfr/rel/set
- **OL Cross-refs**: \olref[set]{sec}, \olref[set][pai]{wienerkuratowski}
- **Notes**: Pure metatheoretical/philosophical discussion. Argues against set-theoretic reductionism via Benacerraf-style arguments. Discusses: (1) non-uniqueness of ordered pair encoding, (2) Russell's paradox for ∈ as a set, (3) Frege's concept horse paradox. Concludes relations are treated as sets, not metaphysically identified with them. No formal content to compress.

### sfr/rel/prp — Special Properties of Relations
- **File**: content/sets-functions-relations/relations/special-properties.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Reflexivity, OL-ONLY: GAP-CANDIDATE: Transitivity, OL-ONLY: GAP-CANDIDATE: Symmetry, OL-ONLY: GAP-CANDIDATE: Anti-symmetry, OL-ONLY: GAP-CANDIDATE: Connectivity, OL-ONLY: GAP-CANDIDATE: Irreflexivity, OL-ONLY: GAP-CANDIDATE: Asymmetry
- **References**: PRIM-BST008
- **OL Formal Items**:
  - \begin{defn}[Reflexivity] → OL-ONLY: GAP-CANDIDATE: Reflexivity (property of relations, not in current taxonomy)
  - \begin{defn}[Transitivity] → OL-ONLY: GAP-CANDIDATE: Transitivity
  - \begin{defn}[Symmetry] → OL-ONLY: GAP-CANDIDATE: Symmetry
  - \begin{defn}[Anti-symmetry] → OL-ONLY: GAP-CANDIDATE: Anti-symmetry
  - \begin{defn}[Connectivity] → OL-ONLY: GAP-CANDIDATE: Connectivity
  - \begin{defn}[Irreflexivity] → OL-ONLY: GAP-CANDIDATE: Irreflexivity
  - \begin{defn}[Asymmetry] → OL-ONLY: GAP-CANDIDATE: Asymmetry
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/rel/set
- **OL Cross-refs**: (none)
- **Notes**: Defines seven fundamental properties that relations can have. These are building blocks for equivalence relations and orders. All seven properties are GAP-CANDIDATES - they should likely be added to BST taxonomy as they are primitive notions used to build DEF-BST004 (Equivalence Relation) and DEF-BST005 (Partial Order).

### sfr/rel/eqv — Equivalence Relations
- **File**: content/sets-functions-relations/relations/equivalence-relations.tex
- **Domain**: BST
- **Introduces**: DEF-BST004, OL-ONLY: GAP-CANDIDATE: Equivalence Class, OL-ONLY: GAP-CANDIDATE: Quotient
- **References**: PRIM-BST008, (implicit: reflexivity, symmetry, transitivity from sfr/rel/prp)
- **OL Formal Items**:
  - \begin{defn}[Equivalence relation] → DEF-BST004 (defining occurrence)
  - \begin{defn}[equivalenceclass] → OL-ONLY: GAP-CANDIDATE: Equivalence Class
  - \begin{prop} (unnamed, about Rxy iff equivalence classes equal) → OL-ONLY: pedagogical (proves equivalence classes partition the set)
  - \begin{ex} (modular arithmetic) → OL-ONLY: pedagogical
- **Role**: DEFINE, PROVE
- **Compression Signal**: CORE-DEF, CORE-THM
- **Ped. Prerequisites**: sfr/rel/set, sfr/rel/prp
- **OL Cross-refs**: (none)
- **Notes**: Defines equivalence relation as reflexive+symmetric+transitive. Introduces equivalence classes [x]_R and quotient A/R. Proves that Rxy iff [x]_R=[y]_R. Example: modular arithmetic ≡_n. The notions of equivalence class and quotient are GAP-CANDIDATES for taxonomy expansion.

### sfr/rel/ord — Orders
- **File**: content/sets-functions-relations/relations/orders.tex
- **Domain**: BST
- **Introduces**: DEF-BST005, OL-ONLY: GAP-CANDIDATE: Preorder, OL-ONLY: GAP-CANDIDATE: Linear Order, OL-ONLY: GAP-CANDIDATE: Strict Order, OL-ONLY: GAP-CANDIDATE: Strict Linear Order, OL-ONLY: GAP-CANDIDATE: Reflexive Closure
- **References**: PRIM-BST008, PRIM-BST003 (⊆), (implicit: reflexivity, transitivity, anti-symmetry, connectivity, irreflexivity, asymmetry from sfr/rel/prp)
- **OL Formal Items**:
  - \begin{defn}[Preorder] → OL-ONLY: GAP-CANDIDATE: Preorder
  - \begin{defn}[Partial order] → DEF-BST005 (defining occurrence)
  - \begin{defn}[Linear order][def:linearorder] → OL-ONLY: GAP-CANDIDATE: Linear Order
  - \begin{defn}[Strict order] → OL-ONLY: GAP-CANDIDATE: Strict Order
  - \begin{defn}[Strict linear order][def:strictlinearorder] → OL-ONLY: GAP-CANDIDATE: Strict Linear Order
  - \begin{prop}[stricttopartial] → OL-ONLY: GAP-CANDIDATE: Reflexive Closure (construction)
  - \begin{prop}[partialtostrict] → OL-ONLY: pedagogical (converse construction)
  - \begin{prop}[extensionality-strictlinearorders] → OL-ONLY: pedagogical (extensionality for strict linear orders)
  - Multiple \begin{ex} → OL-ONLY: pedagogical
- **Role**: DEFINE, PROVE
- **Compression Signal**: CORE-DEF, CORE-THM
- **Ped. Prerequisites**: sfr/rel/set, sfr/rel/prp
- **OL Cross-refs**: \olref[sfr][rel][ord]{prop:stricttopartial}, \olref[sfr][rel][ord]{prop:partialtostrict}
- **Notes**: Defines hierarchy of order types: preorder (reflexive+transitive), partial order (preorder+anti-symmetric), linear order (partial order+connected), strict order (irreflexive+asymmetric+transitive), strict linear order (strict order+connected). Shows conversion between strict and non-strict orders via reflexive closure. Examples: ≤ on ℕ, ⊆ on power sets, divisibility on ℤ, extension on sequences. Multiple GAP-CANDIDATES for taxonomy expansion.

### sfr/rel/grp — Graphs
- **File**: content/sets-functions-relations/relations/graphs.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Directed Graph
- **References**: PRIM-BST008, PRIM-BST001
- **OL Formal Items**:
  - \begin{defn}[Directed graph] → OL-ONLY: GAP-CANDIDATE: Directed Graph
  - \begin{ex} → OL-ONLY: pedagogical (graph examples with diagrams)
- **Role**: DEFINE, APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sfr/rel/set
- **OL Cross-refs**: (none)
- **Notes**: Defines directed graph as G=⟨V,E⟩ where E⊆V². Explains that graphs are just relations with explicit vertex set. Shows visual representation. This is primarily a pedagogical bridge to graph theory; directed graphs are not fundamental to logic foundations but useful for visualization. GAP-CANDIDATE if graph-theoretic concepts are needed elsewhere in OpenLogic.

### sfr/rel/tre — Trees
- **File**: content/sets-functions-relations/relations/trees.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Tree (set-theoretic), OL-ONLY: GAP-CANDIDATE: Well-ordered, OL-ONLY: GAP-CANDIDATE: Minimal Element, OL-ONLY: GAP-CANDIDATE: Successor (in tree), OL-ONLY: GAP-CANDIDATE: Branch, OL-ONLY: pedagogical: König's Lemma
- **References**: DEF-BST005 (Partial Order), PRIM-BST010 (Finite Sequence), PRIM-BST012 (ℕ)
- **OL Formal Items**:
  - \begin{defn}[Tree] → OL-ONLY: GAP-CANDIDATE: Tree (set-theoretic definition)
  - \begin{defn}[Successors] → OL-ONLY: GAP-CANDIDATE: Successor (in tree context)
  - \begin{prop} (unique predecessor) → OL-ONLY: pedagogical
  - \begin{defn} (infinite/finite/finitely branching) → OL-ONLY: pedagogical
  - \begin{defn}[Branches] → OL-ONLY: GAP-CANDIDATE: Branch
  - \begin{prop}[König's lemma] → OL-ONLY: pedagogical (stated without proof)
  - Multiple \begin{ex} → OL-ONLY: pedagogical
- **Role**: DEFINE, PROVE, APPLY
- **Compression Signal**: CORE-DEF, STEPPING-STONE
- **Ped. Prerequisites**: sfr/rel/set, sfr/rel/ord
- **OL Cross-refs**: (none)
- **Notes**: Defines tree as partial order ⟨A,≤⟩ with unique minimal element (root) where {y:y≤z} is well-ordered for all z. Introduces successors/predecessors, branches, finitely branching. Examples: binary tree {0,1}*, ℕ*. States König's lemma. Trees are fundamental for derivation systems, syntax trees, completeness proofs. Multiple GAP-CANDIDATES; tree structure may warrant taxonomy expansion if heavily used in logic parts.

### sfr/rel/ops — Operations on Relations
- **File**: content/sets-functions-relations/relations/operations.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Inverse, OL-ONLY: GAP-CANDIDATE: Relative Product, OL-ONLY: GAP-CANDIDATE: Restriction, OL-ONLY: GAP-CANDIDATE: Application, OL-ONLY: GAP-CANDIDATE: Transitive Closure, OL-ONLY: GAP-CANDIDATE: Reflexive Transitive Closure
- **References**: PRIM-BST008, PRIM-BST012 (ℕ)
- **OL Formal Items**:
  - \begin{defn}[relationoperations] → Multiple operations: Inverse (R⁻¹), Relative Product (R|S), Restriction (R↾A), Application (R[A]) - all OL-ONLY: GAP-CANDIDATE
  - \begin{defn}[Transitive closure] → OL-ONLY: GAP-CANDIDATE: Transitive Closure (R⁺), Reflexive Transitive Closure (R*)
  - Multiple \begin{ex} → OL-ONLY: pedagogical
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/rel/set, sfr/rel/ord
- **OL Cross-refs**: \olref[sfr][rel][ord]{prop:stricttopartial}, \olref[sfr][rel][ord]{prop:partialtostrict}
- **Notes**: Defines six operations on relations: inverse, relative product (composition), restriction to set, application to set, transitive closure, reflexive transitive closure. Examples use successor relation on ℤ and ℕ. All operations are GAP-CANDIDATES. Transitive closure in particular is fundamental for computational semantics and may appear in later chapters. These operations are building blocks for more complex relational reasoning.



### Chapter: inductive-defs-proofs

### sfr/ind/int — Introduction (Induction)
- **File**: content/sets-functions-relations/inductive-defs-proofs/introduction.tex
- **Domain**: BST
- **Introduces**: PRIM-BST013 (Mathematical Induction), PRIM-BST014 (Inductive Definition)
- **References**: PRIM-BST001 (Set), PRIM-BST009 (Function), PRIM-BST012 (ℕ)
- **OL Formal Items**:
  - \begin{defn} (closure under function) → OL-ONLY: stepping stone (set S closed under f iff x∈S → f(x)∈S)
  - \begin{defn} (preserved under function) → OL-ONLY: stepping stone (property P preserved under f iff P(a) → P(f(a)))
  - \begin{defn}[Induction on $\Nat$] → PRIM-BST013 (Mathematical Induction: if P(0) and P preserved under successor, then ∀n P(n))
  - \begin{defn}[Induction on !!{formula}s] → PRIM-BST014 (Inductive Definition: structural induction on inductively defined sets — formulas as the canonical example)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF, PEDAGOGICAL
- **Ped. Prerequisites**: (none — standalone chapter)
- **OL Cross-refs**: (none)
- **Notes**: Introduces induction as a general proof technique. Defines closure and preservation as stepping stones, then states induction on ℕ (PRIM-BST013) and structural induction on formulas (PRIM-BST014). Contains worked example (sum of first n naturals). The formula induction recipe covers all connective cases. This chapter is a single-section standalone — not imported by the main sets-functions-relations part aggregator in some configurations. Related to content/methods/induction/ which has a more detailed treatment.



### Chapter: size-of-sets

### sfr/siz/int — Introduction
- **File**: content/sets-functions-relations/size-of-sets/introduction.tex
- **Domain**: BST
- **Introduces**: None
- **References**: None (informal introduction only)
- **OL Formal Items**: None
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: None
- **OL Cross-refs**: None
- **Notes**: Purely motivational prose. Introduces informal concept of enumerability and Cantor's surprise result about non-enumerable sets. No formal definitions or theorems.

---

### sfr/siz/enm — Enumerations and Enumerable Sets
- **File**: content/sets-functions-relations/size-of-sets/enumerability.tex
- **Domain**: BST
- **Introduces**: PRIM-BST016 (defining occurrence of countability/enumerability), THM-BST002 (ℕ is countably infinite — shown via enumeration)
- **References**: PRIM-BST002 (∈), PRIM-BST009 (Function), DEF-BST002 (Surjection), DEF-BST001 (Injection), DEF-BST003 (Bijection), PRIM-BST004 (∅), PRIM-BST012 (ℕ), PRIM-BST005 (∪)
- **OL Formal Items**:
  - [informal defn of enumeration]: PRIM-BST016
  - [defn:enumerable]: PRIM-BST016
  - [prop:enum-shift]: OL-ONLY: infrastructure (interchanging ℕ and ℤ⁺)
  - [cor:enum-nat]: THM-BST002 (ℕ is enumerable, hence countably infinite)
  - [prop:enum-bij]: OL-ONLY: infrastructure (relating surjections to bijections)
  - [cor:enum-nat-bij]: OL-ONLY: infrastructure
- **Role**: DEFINE, PROVE
- **Compression Signal**: CORE-DEF, CORE-THM
- **Ped. Prerequisites**: sfr/siz/int
- **OL Cross-refs**: None
- **Notes**: Establishes two equivalent formal definitions of enumerability (surjection from ℤ⁺ vs bijection with initial segment). Multiple technical propositions relating different formulations. The corollary that ℕ itself is enumerable maps to THM-BST002. Editorial notes reference alternative treatment in sfr/siz/enm-alt.

---

### sfr/siz/zigzag — Cantor's Zig-Zag Method
- **File**: content/sets-functions-relations/size-of-sets/zig-zag.tex
- **Domain**: BST
- **Introduces**: THM-BST003 (Countable Union of Countable Sets — zig-zag/dovetailing is the core technique)
- **References**: PRIM-BST006 (Ordered Pair), PRIM-BST007 (Cartesian Product), PRIM-BST012 (ℕ), PRIM-BST016 (Enumerability)
- **OL Formal Items**:
  - [prop:natsquaredenumerable]: THM-BST003 (instantiation: ℕ×ℕ enumerable via diagonal traversal)
  - [unnamed prop]: OL-ONLY: stepping stone (ℕⁿ enumerable — generalization)
- **Role**: PROVE, APPLY
- **Compression Signal**: CORE-THM, STEPPING-STONE
- **Ped. Prerequisites**: sfr/siz/enm
- **OL Cross-refs**: sfr/set/pai (conditional reference to ordered pairs)
- **Notes**: Demonstrates the zig-zag/dovetailing technique that underlies THM-BST003. The enumeration of ℕ×ℕ is the canonical instance of "countable union of countable sets is countable." Generalizes to ℕⁿ and (ℤ⁺)* in problems.

---

### sfr/siz/pai — Pairing Functions and Codes
- **File**: content/sets-functions-relations/size-of-sets/pairing.tex
- **Domain**: BST
- **Introduces**: None (pairing functions are encoding technique, not primitive)
- **References**: PRIM-BST006 (Ordered Pair), PRIM-BST007 (Cartesian Product), PRIM-BST012 (ℕ), DEF-BST001 (Injection), PRIM-BST016 (Enumerability)
- **OL Formal Items**: 
  - [defn of pairing function]: OL-ONLY: technique
  - [pairing function formula g(n,m) = ...]: OL-ONLY: examples
- **Role**: APPLY
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/siz/zig
- **OL Cross-refs**: None
- **Notes**: Provides explicit formula for zig-zag enumeration inverse. Many problems apply pairing to show enumerability of ℚ, Bin*, truth functions, finite subsets, cofinite sets, etc.

---

### sfr/siz/pai-alt — An Alternative Pairing Function
- **File**: content/sets-functions-relations/size-of-sets/pairing-alt.tex
- **Domain**: BST
- **Introduces**: None
- **References**: PRIM-BST012 (ℕ), PRIM-BST006 (Ordered Pair), PRIM-BST007 (Cartesian Product), DEF-BST001 (Injection)
- **OL Formal Items**: 
  - [ex: h(n,m) = 2ⁿ(2m+1) - 1]: OL-ONLY: examples
  - [ex: j(n,m) = 2ⁿ3ᵐ]: OL-ONLY: examples
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sfr/siz/pai
- **OL Cross-refs**: None
- **Notes**: Alternative pairing function using powers of 2. Second example uses prime factorization (non-surjective). Pedagogical variation on same theme.

---

### sfr/siz/nen — Non-enumerable Sets
- **File**: content/sets-functions-relations/size-of-sets/non-enumerability.tex
- **Domain**: BST
- **Introduces**: (none — specific instances proved here; general THM-BST001 is in sfr/siz/car)
- **References**: PRIM-BST016 (Enumerability), PRIM-BST011 (Infinite Sequence), PRIM-BST015 (Power Set), PRIM-BST002 (∈), DEF-BST002 (Surjection)
- **OL Formal Items**:
  - [thm:nonenum-bin-omega]: OL-ONLY: stepping stone for THM-BST001 (Bin^ω non-enumerable via diagonal argument)
  - [thm:nonenum-pownat]: OL-ONLY: stepping stone for THM-BST001 (𝒫(ℤ⁺) non-enumerable — specific instance of Cantor's Theorem)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE, CORE-THM
- **Ped. Prerequisites**: sfr/siz/enm
- **OL Cross-refs**: None
- **Notes**: Proves specific non-enumerability results using diagonal technique. OL proves these specific cases BEFORE the general THM-BST001 (in sfr/siz/car). Result (2) is a direct instance of Cantor's Theorem with A=ℤ⁺. Editorial notes reference alternative in sfr/siz/nen-alt.

---

### sfr/siz/red — Reduction
- **File**: content/sets-functions-relations/size-of-sets/reduction.tex
- **Domain**: BST
- **Introduces**: (none — reduction is a proof technique)
- **References**: PRIM-BST016 (Enumerability), PRIM-BST015 (Power Set), PRIM-BST011 (Infinite Sequence), DEF-BST002 (Surjection), DEF-BST001 (Injection)
- **OL Formal Items**: 
  - [Alternative proof of thm:nonenum-pownat]: OL-ONLY: technique demonstration
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/siz/non
- **OL Cross-refs**: sfr/siz/nen (references thm:nonenum-bin-omega and thm:nonenum-pownat)
- **Notes**: Shows reduction technique: 𝒫(ℤ⁺) non-enumerable by reducing from Bin^ω. Problems apply reduction to prove non-enumerability of various sets. Editorial notes reference alternative in sfr/siz/red-alt.

---

### sfr/siz/equ — Equinumerosity
- **File**: content/sets-functions-relations/size-of-sets/equinumerous-sets.tex
- **Domain**: BST
- **Introduces**: None (equinumerosity defined via bijection already primitive)
- **References**: DEF-BST003 (Bijection), DEF-BST004 (Equivalence Relation), PRIM-BST016 (Enumerability), DEF-BST002 (Surjection)
- **OL Formal Items**: 
  - [defn:comparisondef]: OL-ONLY: notation (≈ for equinumerosity)
  - [prop:equinumerosityisequi]: OL-ONLY: infrastructure (equivalence relation)
  - [unnamed prop about enumerable preservation]: OL-ONLY: infrastructure
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sfr/siz/enm
- **OL Cross-refs**: sfr/siz/enm (conditional reference to defn:enumerable)
- **Notes**: Defines equinumerosity relation and proves it's an equivalence relation. Shows enumerability preserved under equinumerosity. Frege quotation motivates bijection-based size comparison.

---

### sfr/siz/car — Sets of Different Sizes, and Cantor's Theorem
- **File**: content/sets-functions-relations/size-of-sets/comparing-size.tex
- **Domain**: BST
- **Introduces**: THM-BST001 (Cantor's Theorem, general form: |A| < |𝒫(A)|)
- **References**: DEF-BST001 (Injection), DEF-BST003 (Bijection), PRIM-BST015 (Power Set), PRIM-BST002 (∈), PRIM-BST016 (Enumerability), DEF-BST002 (Surjection)
- **OL Formal Items**: 
  - [defn: A ≤ B]: OL-ONLY: notation (cardinality comparison)
  - [defn: A < B]: OL-ONLY: notation
  - [thm:cantor]: THM-BST001 (Cantor's Theorem: |A| < |𝒫(A)|)
- **Role**: PROVE, DEFINE
- **Compression Signal**: CORE-THM, CORE-DEF
- **Ped. Prerequisites**: sfr/siz/equ, sfr/siz/non
- **OL Cross-refs**: sfr/siz/nen, sfr/siz/nen-alt (conditional), sfr/set/rus (Russell's Paradox comparison)
- **Notes**: Proves Cantor's Theorem in full generality using diagonalization. Conditional compilation shows detailed proof if nen included, terser proof if nen-alt included. Compares to Russell's Paradox.

---

### sfr/siz/sb — The Notion of Size, and Schröder-Bernstein
- **File**: content/sets-functions-relations/size-of-sets/schroder-bernstein.tex
- **Domain**: BST
- **Introduces**: (none — Schröder-Bernstein stated without proof)
- **References**: DEF-BST001 (Injection), DEF-BST003 (Bijection), PRIM-BST016 (Cardinality)
- **OL Formal Items**:
  - [thm:schroder-bernstein]: OL-ONLY: GAP-CANDIDATE: Schröder-Bernstein Theorem (if A ≤ B and B ≤ A then A ≈ B; stated without proof here, proved in sfr/infinite/card-sb)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/siz/car
- **OL Cross-refs**: sfr/infinite/card-sb (forward reference to proof)
- **Notes**: States Schröder-Bernstein without proof. The theorem is not in the BST taxonomy (GAP-CANDIDATE). Proof deferred to infinite chapter appendix. Explains importance for cardinality comparison.

---

### sfr/siz/enm-alt — Enumerations and Enumerable Sets (alternative)
- **File**: content/sets-functions-relations/size-of-sets/enumerability-alt.tex
- **Domain**: BST
- **Introduces**: PRIM-BST016 (alternative formulation using bijections)
- **References**: PRIM-BST002 (∈), PRIM-BST012 (ℕ), PRIM-BST009 (Function), DEF-BST003 (Bijection), DEF-BST002 (Surjection), DEF-BST001 (Injection)
- **OL Formal Items**: 
  - [defn of enumeration (set-theoretic)]: PRIM-BST016
  - [defn:enumerable]: PRIM-BST016
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: None (alternative to enm)
- **OL Cross-refs**: None
- **Notes**: Alternative definition using bijections with ℕ or initial segments, more standard in set theory. Terser than enm. Editorial notes it conflicts with enm. Examples parallel those in enm.

---

### sfr/siz/nen-alt — Non-enumerable Sets (alternative)
- **File**: content/sets-functions-relations/size-of-sets/non-enumerability-alt.tex
- **Domain**: BST
- **Introduces**: (none — specific instances; general THM-BST001 is in sfr/siz/car)
- **References**: PRIM-BST016 (Enumerability), PRIM-BST011 (Infinite Sequence), PRIM-BST015 (Power Set), PRIM-BST012 (ℕ), DEF-BST003 (Bijection)
- **OL Formal Items**:
  - [thm:nonenum-bin-omega]: OL-ONLY: stepping stone for THM-BST001 (alt formulation using bijections)
  - [thm:nonenum-pownat]: OL-ONLY: stepping stone for THM-BST001 (alt formulation)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE, REDUNDANT-WITH:sfr/siz/nen
- **Ped. Prerequisites**: sfr/siz/enm-alt
- **OL Cross-refs**: sfr/card-arithmetic/card-opps (conditional forward reference)
- **Notes**: Same theorems as sfr/siz/nen but adapted to match sfr/siz/enm-alt enumeration definitions (bijections vs surjections). Slightly more condensed. Alternative version — REDUNDANT with sfr/siz/nen.

---

### sfr/siz/red-alt — Reduction (alternative)
- **File**: content/sets-functions-relations/size-of-sets/reduction-alt.tex
- **Domain**: BST
- **Introduces**: (none — reduction technique)
- **References**: PRIM-BST016 (Enumerability), PRIM-BST015 (Power Set), PRIM-BST011 (Infinite Sequence), PRIM-BST012 (ℕ), DEF-BST002 (Surjection), DEF-BST001 (Injection)
- **OL Formal Items**: 
  - [Alternative proof of thm:nonenum-pownat]: OL-ONLY: technique demonstration
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/siz/noa
- **OL Cross-refs**: sfr/siz/nen-alt (references thm:nonenum-bin-omega and thm:nonenum-pownat)
- **Notes**: Same reduction proof as sfr/siz/red but adapted to match nen-alt formulation. Slightly more condensed. Commented-out explanation section.



### Chapter: infinite

### sfr/infinite/hilbert — Hilbert's Hotel
- **File**: content/sets-functions-relations/infinite/hilberts-hotel.tex
- **Domain**: BST
- **Introduces**: (none — Dedekind infinite is not in taxonomy)
- **References**: PRIM-BST001 (Set), DEF-BST001 (Injection)
- **OL Formal Items**:
  - \begin{defn}[defn:DedekindInfinite] → OL-ONLY: GAP-CANDIDATE: Dedekind Infinite (a set A is Dedekind infinite iff there exists an injection from A to a proper subset of A)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF, PEDAGOGICAL
- **Ped. Prerequisites**: (none, first section in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Introduces Dedekind infinite via Hilbert's hotel metaphor. The concept is a GAP-CANDIDATE — it bridges cardinality (PRIM-BST016) and the algebraic characterization of ℕ developed in subsequent sections. Historical context from Hilbert (1924) and Dedekind (1888). Contains tikz diagram.

---

### sfr/infinite/dedekind — Dedekind Algebras
- **File**: content/sets-functions-relations/infinite/dedekind-algebra.tex
- **Domain**: BST
- **Introduces**: (none — all concepts OL-ONLY)
- **References**: PRIM-BST001 (Set), PRIM-BST003 (Subset), PRIM-BST005 (Intersection), PRIM-BST009 (Function), DEF-BST001 (Injection)
- **OL Formal Items**:
  - \begin{defn}[Closure] → OL-ONLY: GAP-CANDIDATE: f-closed set + closure of o under f (set-theoretic concepts for characterizing ℕ)
  - \begin{lem}[closureproperties] → OL-ONLY: stepping stone (properties of closure: contains o, is f-closed, is smallest such)
  - \begin{defn} (unlabeled, Dedekind algebra) → OL-ONLY: GAP-CANDIDATE: Dedekind Algebra (set A with injection f:A→A, element o∉ran(f), A = closure(f,o))
  - \begin{thm}[thm:DedekindInfiniteAlgebra] → OL-ONLY: stepping stone (Dedekind infinite set → Dedekind algebra exists)
- **Role**: DEFINE, PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/infinite/hilbert
- **OL Cross-refs**: (none)
- **Notes**: Develops Dedekind algebras as a set-theoretic characterization of ℕ. Three properties: (1) 0 not successor, (2) successor is injection, (3) smallest set closed under successor. The closure machinery (f-closed sets, intersection-based closure) is reused in sfr/infinite/card-sb. All concepts here are outside the current taxonomy — Dedekind algebra and closure are GAP-CANDIDATES if Phase 3 needs explicit IDs.

---

### sfr/infinite/induction — Dedekind Algebras and Arithmetical Induction
- **File**: content/sets-functions-relations/infinite/dedekind-induction.tex
- **Domain**: BST
- **Introduces**: (none — induction for Dedekind algebras is OL's grounding of PRIM-BST013)
- **References**: PRIM-BST013 (Mathematical Induction — this section provides the set-theoretic justification)
- **OL Formal Items**:
  - \begin{thm}[thm:dedinfiniteinduction] → OL-ONLY: stepping stone (arithmetical induction: if o∈X and X is s-closed, then N⊆X)
  - \begin{cor}[natinductionschema] → OL-ONLY: stepping stone (formula-based induction schema with parameters)
- **Role**: PROVE, DISCUSS
- **Compression Signal**: STEPPING-STONE, PEDAGOGICAL
- **Ped. Prerequisites**: sfr/infinite/hilbert, sfr/infinite/dedekind
- **OL Cross-refs**: sfr/infinite/dedekind (via \olref[closureproperties]), sth (forward reference to recursive definitions, ordinal arithmetic)
- **Notes**: Shows Dedekind algebras support mathematical induction in both set-theoretic form and formula schema form. This provides the set-theoretic grounding for PRIM-BST013 (Mathematical Induction). Discusses parameters in formulas. Mentions but defers recursive definitions for +, ×, exponentiation.

---

### sfr/infinite/dedekindsproof — Dedekind's "Proof" of the Existence of an Infinite Set
- **File**: content/sets-functions-relations/infinite/dedekinds-proof.tex
- **Domain**: BST
- **Introduces**: (none)
- **References**: (implicit: Dedekind infinite, Dedekind algebra concepts from prior sections)
- **OL Formal Items**: (none — purely discursive)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL, TANGENTIAL
- **Ped. Prerequisites**: sfr/infinite/hilbert, sfr/infinite/dedekind, sfr/infinite/induction
- **OL Cross-refs**: sfr/arith/ref, sfr/infinite/dedekind (thm:DedekindInfiniteAlgebra)
- **Notes**: Philosophical reflection on Dedekind's project to ground arithmetic in logic. Discusses his controversial "proof" of infinite set existence via "realm of thoughts" (§66, Dedekind 1888). Critiques on two grounds: non-mathematical character (psychological) and technical gap (totality vs. set). Motivates transition to axiomatic set theory. No formal results.

---

### sfr/infinite/card-sb — Appendix: Proving Schröder-Bernstein
- **File**: content/sets-functions-relations/infinite/card-sb.tex
- **Domain**: BST
- **Introduces**: (none — proves Schröder-Bernstein which is a GAP-CANDIDATE)
- **References**: PRIM-BST001 (Set), PRIM-BST003 (Subset), PRIM-BST009 (Function), DEF-BST001 (Injection), DEF-BST002 (Surjection), DEF-BST003 (Bijection)
- **OL Formal Items**:
  - \begin{lem}[Closureprops] → OL-ONLY: stepping stone (generalized closure properties for sets, parallels sfr/infinite/dedekind)
  - \begin{prop}[sbhelper] → OL-ONLY: stepping stone (subset sandwich: if A⊆B⊆C and A≈C then A≈B≈C)
  - Proof of Schröder-Bernstein → OL-ONLY: GAP-CANDIDATE: Schröder-Bernstein Theorem (full proof using closure machinery)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sfr/infinite/dedekind (uses closure notation), sfr/siz/sb (states theorem without proof)
- **OL Cross-refs**: sfr/siz/sb (thm:schroder-bernstein), sfr/infinite/dedekind (closure definition)
- **Notes**: Presents Dedekind's elegant proof of Schröder-Bernstein using generalized closure machinery. The theorem itself (GAP-CANDIDATE) is stated in sfr/siz/sb and proved here. Key helper: if A⊆B⊆C and A≈C then A≈B≈C.



### Chapter: arithmetization

### sfr/arith/int — From ℕ to ℤ
- **File**: content/sets-functions-relations/arithmetization/integers.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Integer construction via equivalence classes
- **References**: PRIM-BST006 (Ordered Pair), DEF-BST004 (Equivalence Relation), PRIM-BST012 (Natural Number)
- **OL Formal Items**: 
  - Unnamed proposition (lines 27-37, ℤ-equivalence is equivalence relation): OL-ONLY: pedagogical
  - Unnamed definition (lines 41-43, integers as equivalence classes): OL-ONLY: GAP-CANDIDATE: Integer construction
- **Role**: DEFINE, PROVE
- **Compression Signal**: TANGENTIAL, PEDAGOGICAL
- **Ped. Prerequisites**: (first section in chapter)
- **OL Cross-refs**: sfr/arith/check (line 55), sfr/arith/ref (line 59)
- **Notes**: Constructs ℤ from ℕ×ℕ via equivalence relation ⟨a,b⟩ ≅ ⟨c,d⟩ iff a+d=c+b. Defines operations (+, ×, ≤) and embedding n_ℤ. This construction is TANGENTIAL to the taxonomy, which treats ℕ as primitive and doesn't require constructed number systems. The equivalence relation technique demonstrates DEF-BST004 in practice.

### sfr/arith/rat — From ℤ to ℚ
- **File**: content/sets-functions-relations/arithmetization/rationals.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Rational construction via equivalence classes
- **References**: PRIM-BST006 (Ordered Pair), DEF-BST004 (Equivalence Relation)
- **OL Formal Items**:
  - Unnamed definition (lines 41-45, rationals as equivalence classes): OL-ONLY: GAP-CANDIDATE: Rational construction
- **Role**: DEFINE
- **Compression Signal**: TANGENTIAL, PEDAGOGICAL
- **Ped. Prerequisites**: sfr/arith/int
- **OL Cross-refs**: sfr/arith/check (line 63, 67)
- **Notes**: Constructs ℚ from ℤ×(ℤ\{0}) via equivalence relation ⟨a,b⟩ ≅ ⟨c,d⟩ iff a×d=b×c. Defines operations (+, ×, ≤) and embedding i_ℚ. Parallel construction to integers, similarly TANGENTIAL to taxonomy. Proof of equivalence relation relegated to exercises.

### sfr/arith/real — The Real Line
- **File**: content/sets-functions-relations/arithmetization/reals.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Completeness Property, OL-ONLY: pedagogical: ordered field concept
- **References**: PRIM-BST016 (Cardinality, line 20)
- **OL Formal Items**:
  - \begin{thm}[root2irrational] (lines 25-70, √2 is irrational): OL-ONLY: pedagogical
- **Role**: DISCUSS, PROVE
- **Compression Signal**: PEDAGOGICAL, STEPPING-STONE
- **Ped. Prerequisites**: sfr/arith/int, sfr/arith/rat
- **OL Cross-refs**: sfr/siz (line 19), sfr/arith/check (line 18), his/set/mythology (line 72)
- **Notes**: Motivates the real numbers by distinguishing them from rationals. Proves √2 is irrational (two proofs: geometric and formal). Introduces Completeness Property as the defining feature of ℝ. This is PEDAGOGICAL setup for the construction in sfr/arith/cuts. The Completeness Property is a key concept but not in the BST taxonomy (belongs more to analysis/metatheory of ℝ).

### sfr/arith/cuts — From ℚ to ℝ
- **File**: content/sets-functions-relations/arithmetization/cuts.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Dedekind cut, OL-ONLY: GAP-CANDIDATE: Real construction via cuts
- **References**: PRIM-BST001 (Set), PRIM-BST003 (Subset), PRIM-BST004 (Empty Set)
- **OL Formal Items**:
  - \begin{defn}[Cut] (lines 26-36, Dedekind cut definition): OL-ONLY: GAP-CANDIDATE: Dedekind cut
  - \begin{thm}[realcompleteness] (lines 54-78, cuts have Completeness Property): OL-ONLY: GAP-CANDIDATE: Completeness via cuts
- **Role**: DEFINE, PROVE
- **Compression Signal**: TANGENTIAL, CORE-THM (for Completeness)
- **Ped. Prerequisites**: sfr/arith/rat, sfr/arith/real
- **OL Cross-refs**: sfr/arith/check (lines 40, 112)
- **Notes**: Constructs ℝ as Dedekind cuts (non-empty proper initial segments of ℚ with no maximum). Defines ≤, +, ×, − on cuts. Proves Completeness Property for cuts. This is the classical construction but TANGENTIAL to taxonomy. The proof technique (taking union of a set of cuts) is elegant and uses basic set operations (PRIM-BST001, 003, 004, 005).

### sfr/arith/ref — Some Philosophical Reflections
- **File**: content/sets-functions-relations/arithmetization/reflections.tex
- **Domain**: BST
- **Introduces**: None
- **References**: None (purely philosophical discussion)
- **OL Formal Items**: None
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL, TANGENTIAL
- **Ped. Prerequisites**: sfr/arith/int, sfr/arith/rat, sfr/arith/cuts, sfr/arith/cauchy
- **OL Cross-refs**: sfr/arith/cauchy (lines 28, 68), sfr/rel/ref (line 78), sfr/set/imp (line 88)
- **Notes**: Philosophical commentary on the arithmetization project. Discusses: (1) whether constructions increase rigor, (2) whether we "forget" the constructions in practice, (3) metaphysical status of number systems (Benacerraf-style worries), (4) the oddity that ℕ⊄ℤ under the construction. Pure meta-commentary, no formal content. TANGENTIAL to taxonomy but valuable for understanding limits of formalization.

### sfr/arith/check — Ordered Rings and Fields
- **File**: content/sets-functions-relations/arithmetization/checking-details.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Commutative Ring, OL-ONLY: GAP-CANDIDATE: Ordered Ring, OL-ONLY: GAP-CANDIDATE: Ordered Field
- **References**: DEF-BST004 (Equivalence Relation, implicit in equivalence class operations)
- **OL Formal Items**:
  - Unnamed definition (lines 23-36, commutative ring): OL-ONLY: GAP-CANDIDATE: Commutative Ring
  - Unnamed definition (lines 111-118, ordered ring): OL-ONLY: GAP-CANDIDATE: Ordered Ring
  - \begin{defn}[orderedfield] (lines 131-136, ordered field): OL-ONLY: GAP-CANDIDATE: Ordered Field
- **Role**: DEFINE, PROVE
- **Compression Signal**: TANGENTIAL, STEPPING-STONE
- **Ped. Prerequisites**: sfr/arith/int, sfr/arith/rat, sfr/arith/cuts
- **OL Cross-refs**: sfr/rel/eqv (line 47), sfr/rel/ord (line 106)
- **Notes**: Technical appendix verifying that constructed number systems satisfy algebraic axioms. Proves: ℤ is commutative ring and ordered ring; ℚ is ordered field; ℝ is ordered field. Gives detailed proofs of associativity, additive inverse, distributivity. Also proves √2-cut is indeed a cut. This is TANGENTIAL verification work. The algebraic structure definitions (ring, field) are GAP-CANDIDATES for an algebra domain but outside BST taxonomy scope.

### sfr/arith/cauchy — Appendix: the Reals as Cauchy Sequences
- **File**: content/sets-functions-relations/arithmetization/cauchy.tex
- **Domain**: BST
- **Introduces**: OL-ONLY: GAP-CANDIDATE: Cauchy sequence construction of ℝ
- **References**: PRIM-BST009 (Function), PRIM-BST011 (Infinite Sequence), PRIM-BST012 (Natural Number), DEF-BST004 (Equivalence Relation)
- **OL Formal Items**:
  - \begin{defn}[def:CauchySequence] (lines 83-87, Cauchy sequence): OL-ONLY: GAP-CANDIDATE: Cauchy sequence
  - \begin{thm}[thm:cauchyorderedfield] (lines 161-167, Cauchy sequences form ordered field): OL-ONLY: GAP-CANDIDATE: Cauchy completeness
  - Unnamed theorem (lines 176-227, Cauchy sequences have Completeness Property): OL-ONLY: GAP-CANDIDATE: Completeness via Cauchy
- **Role**: DEFINE, PROVE
- **Compression Signal**: TANGENTIAL, PEDAGOGICAL
- **Ped. Prerequisites**: sfr/arith/rat, sfr/arith/real, sfr/arith/cuts
- **OL Cross-refs**: his/set/limits (lines 76, 116), sfr/arith/check (implicit via orderedfield)
- **Notes**: Alternative construction of ℝ via Cauchy sequences (functions ℕ→ℚ satisfying convergence criterion). Uses equivalence relation f≅g iff (f-g)→0. Defines operations and order, proves ordered field property and Completeness. Historical note mentions Stevin, Weierstrass, Heine, Méray, Cantor. This demonstrates PRIM-BST011 (infinite sequences as functions) in action, but the construction itself is TANGENTIAL. More "modern" than Dedekind cuts but equally outside core taxonomy.

## Batch 2 — SYN+SEM (propositional-logic + first-order-logic/syntax-and-semantics)

### PL syntax-and-semantics

### pl/syn/pre — Preliminaries
- **File**: content/propositional-logic/syntax-and-semantics/preliminaries.tex
- **Domain**: SYN
- **Introduces**: (none)
- **References**: AX-SYN003, DEF-SYN005, DEF-SYN001, THM-SYN001
- **OL Formal Items**:
  - thm:induction → DEF-SYN005 (Principle of induction on formulas)
  - prop:balanced → OL-ONLY: metatheoretic property (balanced parentheses)
  - prop:noinit → OL-ONLY: metatheoretic property (no proper initial segment is formula)
  - Unique Readability (unnamed prop) → THM-SYN001
  - defn:Uniform Substitution → DEF-SYN001
- **Role**: PROVE
- **Variant Tags**: multiple \tagitem for connectives (prvNot, prvAnd, prvOr, prvIf, prvIff)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: pl/syn/fml (referenced via \olref)
- **OL Cross-refs**: \olref[fml]{defn:formulas}
- **Notes**: Proves fundamental metatheoretic properties of PL formulas (induction, unique readability, substitution). These are technical infrastructure theorems.

### pl/syn/int — Introduction
- **File**: content/propositional-logic/syntax-and-semantics/introduction.tex
- **Domain**: SYN and SEM (mixed)
- **Introduces**: (none)
- **References**: PRIM-SYN003, PRIM-SEM015, PRIM-SEM007
- **OL Formal Items**: (none - expository)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none - first section)
- **OL Cross-refs**: (none)
- **Notes**: Conceptual overview of truth-functional propositional logic, syntax vs semantics, inductive definitions. No formal definitions.

### pl/syn/fml — Propositional Formulas
- **File**: content/propositional-logic/syntax-and-semantics/formulas.tex
- **Domain**: SYN
- **Introduces**: PRIM-SYN002 (propositional variable), PRIM-SYN003 (logical connective), PRIM-SYN012 (formula as PL formula), AX-SYN003 (formation rules for PL formulas)
- **References**: (none)
- **OL Formal Items**:
  - defn:formulas → AX-SYN003
  - defn:Syntactic identity → OL-ONLY: technical definition
  - (defined operators section) → OL-ONLY: abbreviations
- **Role**: DEFINE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff, defNot, defOr, defAnd, defIf, defIff, defTrue, defFalse
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: (none)
- **OL Cross-refs**: (none)
- **Notes**: Core definition of PL language and formulas. Atomic formulas are propositional variables plus optional truth constants.

### pl/syn/fseq — Formation Sequences
- **File**: content/propositional-logic/syntax-and-semantics/formation-sequences.tex
- **Domain**: SYN
- **Introduces**: DEF-SYN006 (structural recursion via formation sequences)
- **References**: AX-SYN003, DEF-SYN005
- **OL Formal Items**:
  - defn:fseq-frm → DEF-SYN006
  - prop:formed → OL-ONLY: metatheorem (every formula has formation sequence)
  - lem:fseq-init → OL-ONLY: technical lemma
  - thm:fseq-frm-equiv → OL-ONLY: equivalence of definitions
- **Role**: PROVE
- **Variant Tags**: prvNot, prvAnd, prvOr, prvIf, prvIff
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: pl/syn/fml
- **OL Cross-refs**: \olref[fml]{defn:formulas}, \olref[pl][syn][pre]{prop:noinit}
- **Notes**: Alternative bottom-up construction of formulas. Proves equivalence with inductive definition. Used for some proofs but not essential.

### pl/syn/val — Valuations and Satisfaction
- **File**: content/propositional-logic/syntax-and-semantics/valuations-sat.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM015 (truth-value assignment/valuation), PRIM-SEM007 (satisfaction for PL), DEF-SEM001 (Tarski's satisfaction definition for PL)
- **References**: PRIM-SYN012, PRIM-SEM015
- **OL Formal Items**:
  - defn:valuations → PRIM-SEM015
  - defn:evaluation function → DEF-SEM001 (PL version)
  - defn:satisfaction → PRIM-SEM007
  - thm:LocalDetermination → THM-SEM002 (coincidence lemma for PL)
  - prop:sat-value → OL-ONLY: equivalence of satisfaction and evaluation
- **Role**: DEFINE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: pl/syn/fml
- **OL Cross-refs**: (none)
- **Notes**: Core semantic definitions for PL. Defines valuation as function from variables to truth values, then satisfaction inductively.

### pl/syn/sem — Semantic Notions
- **File**: content/propositional-logic/syntax-and-semantics/semantic-notions.tex
- **Domain**: SEM
- **Introduces**: DEF-SEM002 (satisfiable), DEF-SEM009 (tautology/PL validity), DEF-SEM010 (PL consequence)
- **References**: PRIM-SEM007
- **OL Formal Items**:
  - defn (unnamed, contains 5 items) → DEF-SEM002, DEF-SEM009, DEF-SEM010, OL-ONLY: unsatisfiable, OL-ONLY: contingent
  - prop:semanticalfacts → OL-ONLY: basic properties of semantic notions
  - prop:entails-unsat → OL-ONLY: entailment via unsatisfiability
  - thm:sem-deduction → OL-ONLY: semantic deduction theorem
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: pl/syn/val
- **OL Cross-refs**: \olref[sem]{prop:semanticalfacts}
- **Notes**: Defines core semantic notions (validity, entailment, satisfiability) for PL. Many proofs left as exercises.

### pl/prp/snd — Soundness of Propositional Logic
- **File**: content/propositional-logic/syntax-and-semantics/soundness.tex
- **Domain**: DEDUCTION (metatheory boundary)
- **Introduces**: (none)
- **References**: DEF-SEM010, OL-ONLY: syntactic provability
- **OL Formal Items**:
  - thm:soundness → OL-ONLY: soundness (requires proof system)
  - cor (unnamed) → OL-ONLY: consistency from satisfiability
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: pl/syn/sem, (some proof system chapter)
- **OL Cross-refs**: \olref[sem]{prop:semanticalfacts}
- **Notes**: Connects proof system to semantics. Requires prior definition of $\Proves$ which is not in syntax-and-semantics. File ID is pl/prp/snd not pl/syn/snd.

### pl/prp/com — Completeness of Propositional Logic
- **File**: content/propositional-logic/syntax-and-semantics/completeness.tex
- **Domain**: DEDUCTION (metatheory boundary)
- **Introduces**: (none)
- **References**: OL-ONLY: syntactic provability, DEF-SEM002
- **OL Formal Items**:
  - def:MaxCon → OL-ONLY: maximally consistent (requires proof system)
  - lem:truth → OL-ONLY: truth lemma
  - thm:completeness → OL-ONLY: completeness (requires proof system)
  - cor (unnamed) → OL-ONLY: syntactic from semantic consequence
  - prop:compactness → OL-ONLY: compactness theorem
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: pl/syn/sem, (some proof system chapter)
- **OL Cross-refs**: \olref[axd]{prop:phi}, \olref[axd]{prop:prov-incons}
- **Notes**: Completeness theorem and compactness. Requires proof system. File ID is pl/prp/com not pl/syn/com.

## FOL syntax-and-semantics

### fol/syn/int — Introduction
- **File**: content/first-order-logic/syntax-and-semantics/introduction.tex
- **Domain**: SYN and SEM (mixed)
- **Introduces**: (none)
- **References**: PRIM-SYN010, PRIM-SYN012, PRIM-SYN002, PRIM-SYN005, PRIM-SYN006, PRIM-SYN007, PRIM-SEM001, PRIM-SEM002, PRIM-SEM007, PRIM-SEM009, PRIM-SEM010
- **OL Formal Items**: (none - expository)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none - first section)
- **OL Cross-refs**: (none)
- **Notes**: Conceptual overview of FOL syntax and semantics. Parallel to pl/syn/int.

### fol/syn/itx — Introduction (alternate)
- **File**: content/first-order-logic/syntax-and-semantics/intro-syntax.tex
- **Domain**: SYN
- **Introduces**: (none)
- **References**: PRIM-SYN010, PRIM-SYN012, PRIM-SYN002, PRIM-SYN005, PRIM-SYN006, PRIM-SYN007
- **OL Formal Items**: (none - expository)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none)
- **OL Cross-refs**: (none)
- **Notes**: Shorter syntax-only intro. Appears to be alternate to fol/syn/int for syntax-only builds.

### fol/syn/fol — First-Order Languages
- **File**: content/first-order-logic/syntax-and-semantics/first-order-languages.tex
- **Domain**: SYN
- **Introduces**: PRIM-SYN001 (symbol), PRIM-SYN002 (variable), PRIM-SYN005 (constant), PRIM-SYN006 (function symbol), PRIM-SYN007 (relation/predicate symbol), PRIM-SYN008 (arity), PRIM-SYN009 (language/signature), PRIM-SYN018 (equality symbol), PRIM-SYN003 (logical connective), PRIM-SYN004 (quantifier)
- **References**: (none)
- **OL Formal Items**:
  - (list of symbols and vocabulary) → PRIM-SYN001 through PRIM-SYN009, PRIM-SYN018
  - ex (language of arithmetic) → OL-ONLY: example
  - ex (language of set theory) → OL-ONLY: example
  - ex (language of orders) → OL-ONLY: example
  - (defined symbols section) → OL-ONLY: abbreviations
- **Role**: DEFINE
- **Variant Tags**: prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx, prvFalse, prvTrue, defNot, defOr, defAnd, defIf, defIff, defAll, defEx, defFalse, defTrue
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: (none)
- **OL Cross-refs**: (none)
- **Notes**: Defines the vocabulary of FOL. Lists logical symbols and non-logical symbols that comprise a first-order language.

### fol/syn/frm — Terms and Formulas
- **File**: content/first-order-logic/syntax-and-semantics/terms-formulas.tex
- **Domain**: SYN
- **Introduces**: PRIM-SYN010 (term), PRIM-SYN011 (atomic formula), PRIM-SYN012 (formula), AX-SYN001 (formation rules for terms), AX-SYN002 (formation rules for formulas), DEF-SYN005 (structural induction)
- **References**: PRIM-SYN002, PRIM-SYN005, PRIM-SYN006, PRIM-SYN007, PRIM-SYN009, PRIM-SYN018
- **OL Formal Items**:
  - defn:terms → PRIM-SYN010, AX-SYN001
  - defn:formulas → PRIM-SYN011, PRIM-SYN012, AX-SYN002
  - (defined operators section) → OL-ONLY: abbreviations
  - defn:Syntactic identity → OL-ONLY: technical definition
  - lem:trmind → DEF-SYN005 (for terms)
  - thm:frmind → DEF-SYN005 (for formulas)
- **Role**: DEFINE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx, limitClause, defTrue, defFalse, defNot, defOr, defAnd, defIf, defIff, defAll, defEx
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/fol
- **OL Cross-refs**: (none)
- **Notes**: Core definition of FOL terms and formulas. Includes induction principles.

### fol/syn/fseq — Formation Sequences
- **File**: content/first-order-logic/syntax-and-semantics/formation-sequences.tex
- **Domain**: SYN
- **Introduces**: DEF-SYN006 (structural recursion via formation sequences)
- **References**: PRIM-SYN010, PRIM-SYN011, PRIM-SYN012, AX-SYN001, AX-SYN002, DEF-SYN005, PRIM-SYN017
- **OL Formal Items**:
  - defn:string → OL-ONLY: technical definition
  - defn:fseq-trm → DEF-SYN006 (for terms)
  - defn:fseq-frm → DEF-SYN006 (for formulas)
  - prop:formed → OL-ONLY: every formula has formation sequence
  - lem:fseq-init → OL-ONLY: technical lemma
  - thm:fseq-frm-equiv → OL-ONLY: equivalence of definitions
  - prop:fseq-trm-equiv → OL-ONLY: equivalence for terms
  - defn:minimal-fseq → OL-ONLY: minimal formation sequences
  - prop:subformula-equivs → OL-ONLY: subformula characterizations
- **Role**: PROVE
- **Variant Tags**: prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/syn/frm
- **OL Cross-refs**: (none)
- **Notes**: Alternative bottom-up construction. Proves equivalence with inductive definition. Historical reference to Smullyan.

### fol/syn/unq — Unique Readability
- **File**: content/first-order-logic/syntax-and-semantics/unique-readability.tex
- **Domain**: SYN
- **Introduces**: THM-SYN001 (unique readability for formulas), THM-SYN002 (unique readability for terms, implicit)
- **References**: PRIM-SYN012, AX-SYN002
- **OL Formal Items**:
  - lem (unnamed, balanced parentheses) → OL-ONLY: technical lemma
  - defn:Proper prefix → OL-ONLY: technical definition
  - lem:no-prefix → OL-ONLY: technical lemma
  - prop:unique-atomic → OL-ONLY: unique parsing of atomic formulas
  - prop:Unique Readability → THM-SYN001
- **Role**: PROVE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/syn/frm
- **OL Cross-refs**: (none)
- **Notes**: Proves unique readability for FOL formulas. Essential metatheoretic property.

### fol/syn/mai — Main Operator of a Formula
- **File**: content/first-order-logic/syntax-and-semantics/main-operator.tex
- **Domain**: SYN
- **Introduces**: OL-ONLY: main operator
- **References**: PRIM-SYN012, THM-SYN001
- **OL Formal Items**:
  - def:main-op → OL-ONLY: main operator
  - tab:main-op → OL-ONLY: classification table
- **Role**: DEFINE
- **Variant Tags**: prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx, defNot, defOr, defAnd, defIf, defIff, defEx, defAll, defTrue, defFalse
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/syn/frm, fol/syn/unq
- **OL Cross-refs**: (none)
- **Notes**: Defines notion of main operator. Useful for talking about formula structure. Depends on unique readability.

### fol/syn/sbf — Subformulas
- **File**: content/first-order-logic/syntax-and-semantics/subformulas.tex
- **Domain**: SYN
- **Introduces**: PRIM-SYN017 (subformula), DEF-SYN008 (subterm, implicit)
- **References**: PRIM-SYN012
- **OL Formal Items**:
  - defn:Immediate subformula → PRIM-SYN017 (direct definition)
  - defn:Proper subformula → PRIM-SYN017 (recursive definition)
  - defn:subformula → PRIM-SYN017
  - prop:subfrm-trans → OL-ONLY: transitivity
  - prop:count-subfrms → OL-ONLY: counting bound
- **Role**: DEFINE
- **Variant Tags**: prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/frm
- **OL Cross-refs**: (none)
- **Notes**: Defines subformula relation recursively. Essential for structural reasoning about formulas.

### fol/syn/fvs — Free Variables and Sentences
- **File**: content/first-order-logic/syntax-and-semantics/free-vars-sentences.tex
- **Domain**: SYN
- **Introduces**: PRIM-SYN014 (free occurrence), PRIM-SYN015 (bound occurrence), PRIM-SYN016 (scope), PRIM-SYN013 (sentence), DEF-SYN003 (free variables FV(φ))
- **References**: PRIM-SYN012, PRIM-SYN002, PRIM-SYN004
- **OL Formal Items**:
  - defn:free-occ → PRIM-SYN014
  - defn:Bound Variables → PRIM-SYN015
  - defn:Scope → PRIM-SYN016
  - defn:Sentence → PRIM-SYN013
  - ex (unnamed) → OL-ONLY: examples
- **Role**: DEFINE
- **Variant Tags**: prvNot, prvAll, prvEx
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/frm
- **OL Cross-refs**: (none)
- **Notes**: Defines free/bound occurrences, scope, and sentences. Essential for semantics.

### fol/syn/sub — Substitution
- **File**: content/first-order-logic/syntax-and-semantics/substitution.tex
- **Domain**: SYN
- **Introduces**: DEF-SYN001 (substitution), OL-ONLY: free for (capture-avoiding condition)
- **References**: PRIM-SYN010, PRIM-SYN012, PRIM-SYN014, PRIM-SYN016
- **OL Formal Items**:
  - defn:Substitution in a term → DEF-SYN001 (for terms)
  - defn:free for → OL-ONLY: technical condition
  - defn:Substitution in a formula → DEF-SYN001 (for formulas)
  - ex (unnamed) → OL-ONLY: examples
- **Role**: DEFINE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/frm, fol/syn/fvs
- **OL Cross-refs**: (none)
- **Notes**: Defines substitution recursively. Introduces "free for" condition to avoid variable capture.

### fol/syn/its — Introduction (semantics)
- **File**: content/first-order-logic/syntax-and-semantics/intro-semantics.tex
- **Domain**: SEM
- **Introduces**: (none)
- **References**: PRIM-SEM001, PRIM-SEM002, PRIM-SEM003, PRIM-SEM004, PRIM-SEM007, PRIM-SEM009, PRIM-SEM010
- **OL Formal Items**: (none - expository)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (syntax sections)
- **OL Cross-refs**: (none)
- **Notes**: Conceptual overview of FOL semantics: structures, variable assignments, satisfaction, validity.

### fol/syn/str — Structures for First-order Languages
- **File**: content/first-order-logic/syntax-and-semantics/structures.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM001 (structure), PRIM-SEM002 (domain), PRIM-SEM003 (interpretation)
- **References**: PRIM-SYN005, PRIM-SYN006, PRIM-SYN007, PRIM-SYN009
- **OL Formal Items**:
  - defn:structures → PRIM-SEM001, PRIM-SEM002, PRIM-SEM003
  - ex (standard model of arithmetic) → OL-ONLY: example
  - ex (structures for set theory) → OL-ONLY: example
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/fol
- **OL Cross-refs**: (none)
- **Notes**: Defines structures (domain + interpretation function). Examples include standard model of arithmetic and hereditarily finite sets.

### fol/syn/cov — Covered Structures
- **File**: content/first-order-logic/syntax-and-semantics/covered-structures.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM006 (term valuation for closed terms), OL-ONLY: covered structure
- **References**: PRIM-SEM001, PRIM-SEM003, PRIM-SYN010
- **OL Formal Items**:
  - defn:value of closed terms → PRIM-SEM006
  - defn:Covered structure → OL-ONLY: special kind of structure
  - ex (unnamed) → OL-ONLY: example
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/syn/str, fol/syn/frm
- **OL Cross-refs**: (none)
- **Notes**: Defines value of closed terms and covered structures. Special case before general variable assignments.

### fol/syn/sat — Satisfaction of a Formula in a Structure
- **File**: content/first-order-logic/syntax-and-semantics/satisfaction.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM004 (variable assignment), PRIM-SEM005 (x-variant), PRIM-SEM006 (term valuation), PRIM-SEM007 (satisfaction), DEF-SEM001 (Tarski's satisfaction definition)
- **References**: PRIM-SEM001, PRIM-SEM002, PRIM-SEM003, PRIM-SYN002, PRIM-SYN010, PRIM-SYN011, PRIM-SYN012
- **OL Formal Items**:
  - defn:Variable Assignment → PRIM-SEM004
  - defn:value of Terms → PRIM-SEM006
  - defn:x-Variant → PRIM-SEM005
  - defn (unnamed, $\Subst{s}{m}{x}$) → PRIM-SEM005 (specific x-variant)
  - defn:satisfaction → PRIM-SEM007, DEF-SEM001
  - ex (large example) → OL-ONLY: worked examples
  - prop:sat-ex → OL-ONLY: existential quantifier property
  - prop:sat-all → OL-ONLY: universal quantifier property
- **Role**: DEFINE
- **Variant Tags**: prvFalse, prvTrue, prvNot, prvAnd, prvOr, prvIf, prvIff, prvAll, prvEx, defEx, defAll
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/str, fol/syn/frm
- **OL Cross-refs**: \olref[ass]{prop:sat-quant}, \olref[ext]{prop:ext-formulas}, \olref[ass]{prop:sentence-sat-true}
- **Notes**: Central definition of satisfaction. Defines variable assignments, term valuation, and satisfaction relation inductively.

### fol/syn/ext — Extensionality
- **File**: content/first-order-logic/syntax-and-semantics/extensionality.tex
- **Domain**: SEM
- **Introduces**: THM-SEM002 (coincidence lemma), THM-SYN003 (substitution lemma)
- **References**: PRIM-SEM001, PRIM-SEM004, PRIM-SEM007, PRIM-SEM006, DEF-SYN001
- **OL Formal Items**:
  - prop:extensionality → THM-SEM002
  - cor:extensionality-sent → THM-SEM002 (for sentences)
  - prop:ext-terms → THM-SYN003 (substitution lemma for terms)
  - prop:ext-formulas → THM-SYN003 (substitution lemma for formulas)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/syn/sat, fol/syn/sub
- **OL Cross-refs**: \olref[ass]{cor:sat-sentence}
- **Notes**: Proves extensionality (coincidence lemma) and substitution lemma. Key metatheoretic results.

### fol/syn/sem — Semantic Notions
- **File**: content/first-order-logic/syntax-and-semantics/semantic-notions.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM009 (logical validity), PRIM-SEM010 (logical consequence), PRIM-SEM011 (model), DEF-SEM002 (satisfiable), DEF-SEM004 (semantic consistency — "has a model", same as satisfiable)
- **References**: PRIM-SEM001, PRIM-SEM007, PRIM-SEM013
- **OL Formal Items**:
  - defn:Validity → PRIM-SEM009
  - defn:Entailment → PRIM-SEM010
  - defn:Satisfiability → DEF-SEM002, PRIM-SEM011
  - prop (unnamed, validity characterization) → OL-ONLY: basic property
  - prop:entails-unsat → OL-ONLY: entailment via unsatisfiability
  - prop (unnamed, monotonicity) → OL-ONLY: basic property
  - thm:sem-deduction → OL-ONLY: semantic deduction theorem
  - prop:quant-terms → OL-ONLY: quantifier instantiation/generalization
- **Role**: DEFINE
- **Variant Tags**: prvEx, prvAll, probEx, probAll
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/syn/sat
- **OL Cross-refs**: \olref[ext]{prop:ext-formulas}, \olref[ass]{prop:sat-quant}, \olref[ass]{prop:sentence-sat-true}
- **Notes**: Defines core semantic notions (validity, entailment, satisfiability) for FOL. Analogous to pl/syn/sem.

### fol/syn/ass — Variable Assignments
- **File**: content/first-order-logic/syntax-and-semantics/assignments.tex
- **Domain**: SEM
- **Introduces**: PRIM-SEM008 (Truth in a Structure — $\mathfrak{A} \vDash \varphi$ for sentences)
- **References**: PRIM-SEM004, PRIM-SEM006, PRIM-SEM007, PRIM-SYN013, PRIM-SYN014
- **OL Formal Items**:
  - prop:valindep → OL-ONLY: value depends only on variables in term
  - prop:satindep → OL-ONLY: satisfaction depends only on free variables
  - cor:sat-sentence → OL-ONLY: sentences don't depend on assignment
  - defn:satisfaction (for sentences) → PRIM-SEM008 (truth in structure)
  - defn:sat (for sets) → PRIM-SEM011 (model, alternative formulation)
  - prop:sentence-sat-true → OL-ONLY: equivalence of sentence satisfaction notions
  - prop:sat-quant → OL-ONLY: quantifier satisfaction for sentences
- **Role**: PROVE
- **Variant Tags**: prvTrue, prvFalse, probNot, probAnd, probOr, probIf, probIff, probEx, probAll
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/syn/sat
- **OL Cross-refs**: (none)
- **Notes**: Proves that satisfaction depends only on free variables. Justifies defining satisfaction for sentences without assignments.

---

## Summary Statistics

**Total files mapped**: 25 (8 PL + 17 FOL)

**Domain distribution**:
- Pure SYN: 12 files
- Pure SEM: 8 files
- Mixed SYN/SEM: 2 files (intro sections)
- DEDUCTION boundary: 2 files (soundness, completeness)
- Tangential (outside core SYN/SEM): 1 file

**Compression signals**:
- CORE-DEF: 13 files
- CORE-THM: 5 files
- STEPPING-STONE: 3 files
- PEDAGOGICAL: 3 files
- TANGENTIAL: 2 files

**Taxonomy coverage from SYN registry (33 items)**:
- **Introduced in these files**: 29 items
  - PRIMs: PRIM-SYN001 through PRIM-SYN018 (all 18)
  - AXs: AX-SYN001, AX-SYN002, AX-SYN003 (all 3)
  - DEFs: DEF-SYN001, DEF-SYN003, DEF-SYN005, DEF-SYN006, DEF-SYN008 (5 of 8)
  - THMs: THM-SYN001, THM-SYN002 (2 of 4)
- **Not introduced** (assumed elsewhere or not in these chapters): 4 items
  - DEF-SYN002 (simultaneous substitution - mentioned but not formally defined)
  - DEF-SYN004 (alphabetic variant - not mentioned)
  - DEF-SYN007 (formula complexity/rank - not mentioned)
  - THM-SYN003 (substitution lemma - for syntax, FOL version is semantic)
  - THM-SYN004 (structural induction/recursion principles - stated as lemmas, not proven as theorems)

**Taxonomy coverage from SEM registry (34 items)**:
- **Introduced in these files**: 21 items
  - PRIMs: PRIM-SEM001 through PRIM-SEM015 (all 15)
  - DEFs: DEF-SEM001, DEF-SEM002, DEF-SEM009, DEF-SEM010 (4 of 16)
  - THMs: THM-SEM002 (1 of 3; THM-SYN003 substitution lemma is in SYN domain)
- **Not introduced** (assumed in other chapters): 13 items
  - Most DEFs are model-theoretic concepts not covered in basic syntax-and-semantics (e.g., DEF-SEM003 finitely satisfiable, DEF-SEM006 theory of structure, DEF-SEM007 definable set, DEF-SEM011 elementary substructure, DEF-SEM012 diagram, DEF-SEM013 type, DEF-SEM014 categoricity, DEF-SEM015 ultraproduct, DEF-SEM016 embedding)
  - PRIM-SEM012 (isomorphism), PRIM-SEM013 (substructure), PRIM-SEM014 (homomorphism) - covered in model theory chapters
  - THM-SEM001 (isomorphism lemma) - in model theory

**OL-ONLY concepts** (not in taxonomy): Approximately 40+ items including:
- Metatheoretic properties (balanced formulas, no proper prefix, etc.)
- Technical definitions (syntactic identity, proper prefix, strings, minimal formation sequences)
- Proof-system dependent notions (maximally consistent, soundness, completeness, compactness)
- Examples and worked problems
- Auxiliary lemmas and propositions

## Batch 2 Supplement: fol/int/ — First-Order Logic Introduction (9 sections)

### fol/int/fol — First-Order Logic
- **File**: content/first-order-logic/introduction/first-order-logic.tex
- **Domain**: SYN+SEM+DED
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SYN011 (Formula), PRIM-SYN013 (Sentence), PRIM-SEM001 (Structure), PRIM-SEM005 (Satisfaction), PRIM-SEM009 (Entailment), PRIM-DED006 (Provability), CP-001 (Soundness), CP-002 (Completeness)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none — first section)
- **OL Cross-refs**: (none)
- **Notes**: Chapter-opening overview of FOL: syntax, semantics, deduction. Motivates the three main themes and the role of meta-logical proofs.

---

### fol/int/syn — Syntax
- **File**: content/first-order-logic/introduction/syntax.tex
- **Domain**: SYN
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SYN005 (Constant Symbol), PRIM-SYN007 (Relation Symbol), PRIM-SYN011 (Formula), PRIM-SYN013 (Sentence), PRIM-SYN002 (Logical Connective), PRIM-SYN003 (Quantifier), PRIM-SYN004 (Variable)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol
- **OL Cross-refs**: (none)
- **Notes**: Informal syntax overview: vocabulary, domain-specific vs logical symbols, motivation for precise definitions.

---

### fol/int/fml — Formulas
- **File**: content/first-order-logic/introduction/formulas.tex
- **Domain**: SYN
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SYN011 (Formula), PRIM-SYN004 (Variable), PRIM-SYN005 (Constant Symbol), PRIM-SYN007 (Relation Symbol), PRIM-SYN002 (Logical Connective), PRIM-SYN003 (Quantifier), PRIM-SYN013 (Sentence), PRIM-SYN012 (Free/Bound Variable)
- **OL Formal Items**: \begin{defn} (simplified formula definition for toy language)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn
- **OL Cross-refs**: \olref[mth][ind][idf]{sec}, \olref[mth][ind][sti]{sec}
- **Notes**: Simplified inductive definition of formula for toy language. Introduces structural induction concept. Full definition deferred to later chapters.

---

### fol/int/snt — Sentences
- **File**: content/first-order-logic/introduction/sentences.tex
- **Domain**: SYN
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SYN013 (Sentence), PRIM-SYN011 (Formula), PRIM-SYN012 (Free/Bound Variable), PRIM-SYN003 (Quantifier), PRIM-SYN004 (Variable)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml
- **OL Cross-refs**: (none)
- **Notes**: Sketches free/bound variable definitions. Defines sentence as formula with no free variables.

---

### fol/int/sub — Substitution
- **File**: content/first-order-logic/introduction/substitution.tex
- **Domain**: SYN
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SYN010 (Term), PRIM-SYN011 (Formula), PRIM-SYN004 (Variable), PRIM-SYN005 (Constant Symbol), PRIM-SYN006 (Function Symbol), PRIM-DED006 (Provability), PRIM-SEM009 (Entailment), PRIM-SEM004 (Variable Assignment), PRIM-SEM005 (Satisfaction)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt
- **OL Cross-refs**: (none)
- **Notes**: Motivates substitution: needed for inference rules (universal instantiation). Notes subtlety of variable capture.

---

### fol/int/sat — Satisfaction
- **File**: content/first-order-logic/introduction/satisfaction.tex
- **Domain**: SEM
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SEM001 (Structure), PRIM-SEM002 (Domain), PRIM-SEM003 (Interpretation), PRIM-SEM005 (Satisfaction), PRIM-SEM004 (Variable Assignment), PRIM-SYN011 (Formula), PRIM-SYN004 (Variable), PRIM-SYN005 (Constant Symbol), PRIM-SYN007 (Relation Symbol)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub
- **OL Cross-refs**: (none)
- **Notes**: Sketches satisfaction definition for toy language. Introduces structures, variable assignments, and Sat{M}{A}[s] notation.

---

### fol/int/sem — Semantic Notions
- **File**: content/first-order-logic/introduction/semantic-notions.tex
- **Domain**: SEM
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SEM005 (Satisfaction), PRIM-SEM004 (Variable Assignment), PRIM-SYN012 (Free/Bound Variable), PRIM-SYN013 (Sentence), PRIM-SEM007 (Validity/Logical Truth), PRIM-SEM009 (Entailment), PRIM-SEM001 (Structure)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat
- **OL Cross-refs**: (none)
- **Notes**: Defines validity, entailment, satisfiability informally. Notes sentences are independent of variable assignment.

---

### fol/int/mod — Models and Theories
- **File**: content/first-order-logic/introduction/models-theories.tex
- **Domain**: SEM
- **Introduces**: (none — introductory overview)
- **References**: PRIM-SEM001 (Structure), PRIM-SEM011 (Model), PRIM-SEM012 (Theory of Structure), PRIM-SEM009 (Entailment), PRIM-SYN013 (Sentence), CP-003 (Compactness)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat, fol/int/sem
- **OL Cross-refs**: (none)
- **Notes**: Introduces model theory informally. Preorder axiomatization example. Notes expressiveness limits (compactness, Löwenheim-Skolem).

---

### fol/int/scp — Soundness and Completeness
- **File**: content/first-order-logic/introduction/soundness-completeness.tex
- **Domain**: DED
- **Introduces**: (none — introductory overview)
- **References**: PRIM-DED006 (Provability), PRIM-SEM009 (Entailment), DEF-DED001 (Syntactic Consistency), CP-001 (Soundness), CP-002 (Completeness), CP-003 (Compactness)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat, fol/int/sem, fol/int/mod
- **OL Cross-refs**: (none)
- **Notes**: Introduces derivation systems, soundness, completeness informally. Notes completeness implies compactness and Löwenheim-Skolem.

---

## Batch 3 — DED (first-order-logic deduction chapters)


### Chapter: axiomatic-deduction

### fol/axd/rul — Rules and Derivation
- **File**: content/first-order-logic/axiomatic-deduction/rules-and-proofs.tex
- **Domain**: DED
- **Introduces**: PRIM-DED005 (Derivation), PRIM-DED006 (Provability), PRIM-DED010 (Theorem)
- **References**: PRIM-DED003 (Rule of Inference), PRIM-DED001 (Axiom Schema), AX-DED001 (Modus Ponens), PRIM-SYN012 (Formula)
- **OL Formal Items**:
  - defn(Derivability) → PRIM-DED005: Derivation
  - defn(Rule of Inference) → PRIM-DED003: Rule of Inference
  - defn(Derivability) → PRIM-DED006: Provability (Γ⊢φ)
  - defn(Theorems) → PRIM-DED010: Theorem
- **Role**: DEFINE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/rul, PL=pl/axd/rul
- **Compression Signal**: CORE-DEF (foundational definitions for axiomatic proofs)
- **Ped. Prerequisites**: (none, chapter introduction)
- **OL Cross-refs**: (none in this section)
- **Notes**: Establishes the basic framework of axiomatic derivation: sequences of formulas justified by axioms or modus ponens. Defines the ⊢ relation.

---


### fol/axd/prv — Derivability and Consistency
- **File**: content/first-order-logic/axiomatic-deduction/provability-consistency.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), DEF-DED001 (Syntactic Consistency), THM-DED001 (Deduction Theorem)
- **OL Formal Items**:
  - prop(provability-contr) → OL-ONLY: contradiction property
  - prop(prov-incons) → OL-ONLY: derivability iff inconsistency of negation
  - prop(explicit-inc) → OL-ONLY: explicit inconsistency
  - prop(provability-exhaustive) → OL-ONLY: exhaustion principle
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/prv, PL=pl/axd/prv
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/axd/ptn, fol/axd/ded, fol/axd/prp
- **OL Cross-refs**: olref[ptn]{prop:*}, olref[prp]{ax:*}, olref[ded]{prop:mp}
- **Notes**: Properties of consistency relation. Needed for maximal consistent sets in completeness proof.
  Note: provability.tex also exists with same olfileid but is NOT imported by chapter file.

---


### fol/axd/ptn — Proof-Theoretic Notions
- **File**: content/first-order-logic/axiomatic-deduction/proof-theoretic-notions.tex
- **Domain**: DED
- **Introduces**: PRIM-DED006 (Provability), PRIM-DED010 (Theorem), DEF-DED001 (Syntactic Consistency)
- **References**: PRIM-SEM009 (Validity), PRIM-SEM010 (Logical Consequence)
- **OL Formal Items**:
  - defn(Derivability) → PRIM-DED006: Provability
  - defn(Theorems) → PRIM-DED010: Theorem
  - defn(Consistency) → DEF-DED001: Syntactic Consistency
  - prop(reflexivity) → OL-ONLY: structural property
  - prop(monotonicity) → OL-ONLY: structural property
  - prop(transitivity) → OL-ONLY: structural property (cut)
  - prop(incons) → OL-ONLY: inconsistency characterization
  - prop(proves-compact) → OL-ONLY: compactness property
- **Role**: DEFINE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/ptn, PL=pl/axd/ptn
- **Compression Signal**: CORE-DEF (foundational proof-theoretic concepts)
- **Ped. Prerequisites**: fol/axd/rul
- **OL Cross-refs**: (none)
- **Notes**: Parallel to semantic notions. Establishes reflexivity, monotonicity, transitivity, compactness. Dual with natural deduction version.

---


### fol/axd/ppr — Derivability and Propositional Connectives
- **File**: content/first-order-logic/axiomatic-deduction/provability-propositional.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), PRIM-SYN003 (Logical Connective), AX-DED001 (Modus Ponens), THM-DED001 (Deduction Theorem)
- **OL Formal Items**:
  - prop(provability-land) → OL-ONLY: conjunction properties
  - prop(provability-lor) → OL-ONLY: disjunction properties
  - prop(provability-lif) → OL-ONLY: implication properties
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/ppr, PL=pl/axd/ppr
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/axd/rul, fol/axd/prp, fol/axd/ded
- **OL Cross-refs**: olref[prp]{ax:*}
- **Notes**: Establishes basic facts about connectives needed for completeness. Dual with natural deduction version.

---


### fol/axd/qpr — Derivability and Quantifiers
- **File**: content/first-order-logic/axiomatic-deduction/provability-quantifiers.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), PRIM-SYN004 (Quantifier), AX-DED002 (Universal Generalization), THM-DED001 (Deduction Theorem)
- **OL Formal Items**:
  - thm(strong-generalization) → OL-ONLY: strong generalization on constants
  - prop(provability-quantifiers) → OL-ONLY: quantifier instantiation/introduction
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL
- **Dual ID**: FOL=fol/axd/qpr
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/axd/rul, fol/axd/qua, fol/axd/ded
- **OL Cross-refs**: olref[qua]{ax:q1}, olref[qua]{ax:q2}
- **Notes**: FOL-only. Establishes quantifier facts needed for completeness.

---


### fol/axd/ded — Deduction Theorem
- **File**: content/first-order-logic/axiomatic-deduction/deduction-theorem.tex
- **Domain**: DED
- **Introduces**: THM-DED001 (Deduction Theorem), CP-009 (Deduction Theorem as composition pattern)
- **References**: PRIM-DED006 (Provability), AX-DED001 (Modus Ponens)
- **OL Formal Items**:
  - prop(mp) → AX-DED001: Modus Ponens (meta-level)
  - thm(deduction-thm) → THM-DED001 / CP-009: Deduction Theorem
  - prop(derivfacts) → OL-ONLY: derived facts (contraposition, explosion, DNE)
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/ded, PL=pl/axd/ded
- **Compression Signal**: CORE-THM (fundamental metatheorem)
- **Ped. Prerequisites**: fol/axd/rul, fol/axd/ptn, fol/axd/prp
- **OL Cross-refs**: olref[ptn]{prop:*}, olref[prp]{ax:*}, olref[pro]{ex:identity}
- **Notes**: Central result enabling reasoning about ⊢. Proof by induction on derivation length. Used extensively in subsequent proofs. CP-009 in taxonomy.

---


### fol/axd/ide — Derivation with Identity
- **File**: content/first-order-logic/axiomatic-deduction/identity.tex
- **Domain**: DED
- **Introduces**: (none, extends system)
- **References**: PRIM-DED006 (Provability), PRIM-DED001 (Axiom Schema), AX-DED001 (Modus Ponens)
- **OL Formal Items**:
  - defn(Axioms for identity) → OL-ONLY: identity axioms (extension)
  - prop(sound) → OL-ONLY: validity of identity axioms
  - prop(iden1) → OL-ONLY: reflexivity of identity
  - prop(iden2) → OL-ONLY: substitutivity (Leibniz Law)
- **Role**: APPLY
- **Variant Tags**: prfAX, FOL
- **Dual ID**: FOL=fol/axd/ide
- **Compression Signal**: PEDAGOGICAL (extension to system)
- **Ped. Prerequisites**: fol/axd/rul
- **OL Cross-refs**: (none)
- **Notes**: Adds identity axioms. Simple extension pattern.

---


### fol/axd/sou — Soundness
- **File**: content/first-order-logic/axiomatic-deduction/soundness.tex
- **Domain**: DED
- **Introduces**: CP-001 (Soundness Theorem — primary proof for Hilbert system)
- **References**: PRIM-DED006 (Provability), PRIM-SEM009 (Validity), PRIM-SEM010 (Logical Consequence), PRIM-SEM007 (Satisfaction), DEF-DED001 (Syntactic Consistency), DEF-DED005 (Hilbert-Style Proof System)
- **OL Formal Items**:
  - prop(axioms valid) → OL-ONLY: stepping stone for CP-001
  - thm(soundness) → CP-001: soundness theorem (Γ⊢φ → Γ⊨φ)
  - cor(weak-soundness) → OL-ONLY: corollary of CP-001
  - cor(consistency-soundness) → OL-ONLY: corollary of CP-001 (satisfiability → consistency)
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/sou, PL=pl/axd/sou
- **Compression Signal**: CORE-THM (soundness metatheorem)
- **Ped. Prerequisites**: fol/axd/rul, fol/axd/ptn, semantics chapter
- **OL Cross-refs**: olref[syn][ext]{prop:*}, olref[syn][sem]{thm:sem-deduction}
- **Notes**: Proof by induction on derivation. Dual with natural deduction soundness.

---


### fol/axd/prp — Axioms and Rules for Propositional Connectives
- **File**: content/first-order-logic/axiomatic-deduction/axioms-rules-propositional.tex
- **Domain**: DED
- **Introduces**: PRIM-DED001 (Axiom Schema), AX-DED003 (Logical Axiom Schemas - Hilbert), AX-DED001 (Modus Ponens), DEF-DED005 (Hilbert-Style Proof System)
- **References**: PRIM-DED003 (Rule of Inference), PRIM-SYN003 (Logical Connective)
- **OL Formal Items**:
  - defn(Axioms) → AX-DED003: 14 axiom schemas for connectives
  - defn(Modus ponens) → AX-DED001: Modus Ponens
- **Role**: DEFINE
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/prp, PL=pl/axd/prp
- **Compression Signal**: CORE-DEF (defines the axiomatic system)
- **Ped. Prerequisites**: (none, system specification)
- **OL Cross-refs**: (none)
- **Notes**: Specifies the Hilbert system for propositional logic. 14 axiom schemas covering ∧, ∨, →, ¬, ⊤, ⊥, plus MP rule.

---


### fol/axd/qua — Axioms and Rules for Quantifiers
- **File**: content/first-order-logic/axiomatic-deduction/axioms-rules-quantifiers.tex
- **Domain**: DED
- **Introduces**: AX-DED003 (Logical Axiom Schemas - quantifier portion), AX-DED002 (Universal Generalization)
- **References**: PRIM-DED001 (Axiom Schema), PRIM-DED003 (Rule of Inference), PRIM-SYN004 (Quantifier)
- **OL Formal Items**:
  - defn(Axioms for quantifiers) → AX-DED003: ∀ and ∃ axioms
  - defn(Rules for quantifiers) → PRIM-DED003: quantifier rule (QR)
- **Role**: DEFINE
- **Variant Tags**: prfAX, FOL
- **Dual ID**: FOL=fol/axd/qua
- **Compression Signal**: CORE-DEF (extends system to FOL)
- **Ped. Prerequisites**: fol/axd/prp
- **OL Cross-refs**: (none)
- **Notes**: Adds quantifier axioms and QR inference rule. FOL-only. Completes specification of Hilbert system for FOL.

---


### fol/axd/ddq — Deduction Theorem with Quantifiers
- **File**: content/first-order-logic/axiomatic-deduction/deduction-theorem-quantifiers.tex
- **Domain**: DED
- **Introduces**: (none, extends theorem)
- **References**: THM-DED001 (Deduction Theorem), PRIM-DED003 (Rule of Inference), AX-DED001 (Modus Ponens)
- **OL Formal Items**:
  - thm(deduction-thm-q) → THM-DED001: Deduction Theorem (FOL version)
- **Role**: PROVE
- **Variant Tags**: prfAX, FOL
- **Dual ID**: FOL=fol/axd/ddq
- **Compression Signal**: STEPPING-STONE (extends core theorem to FOL)
- **Ped. Prerequisites**: fol/axd/ded, fol/axd/qua
- **OL Cross-refs**: olref[ded]{thm:deduction-thm}
- **Notes**: Extends deduction theorem to handle QR rule. Additional case in inductive proof.

---


### fol/axd/pro — Examples of Derivation
- **File**: content/first-order-logic/axiomatic-deduction/proving-things.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED005 (Derivation), AX-DED001 (Modus Ponens), AX-DED003 (Logical Axiom Schemas)
- **OL Formal Items**:
  - ex(multiple examples) → OL-ONLY: pedagogical examples
  - ex(identity) → OL-ONLY: derivation of D→D
  - ex(chain) → OL-ONLY: transitivity of implication
  - prop(chain) → OL-ONLY: meta-level transitivity
- **Role**: APPLY
- **Variant Tags**: prfAX, FOL/PL
- **Dual ID**: FOL=fol/axd/pro, PL=pl/axd/pro
- **Compression Signal**: PEDAGOGICAL (teaching by example)
- **Ped. Prerequisites**: fol/axd/rul, fol/axd/prp
- **OL Cross-refs**: olref[prp]{ax:*}
- **Notes**: Concrete derivations to illustrate the system. Shows strategies for finding proofs.

---


### fol/axd/prq — Derivation with Quantifiers
- **File**: content/first-order-logic/axiomatic-deduction/proving-things-quant.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED005 (Derivation), PRIM-SYN004 (Quantifier), AX-DED001 (Modus Ponens), PRIM-DED003 (Rule of Inference)
- **OL Formal Items**:
  - ex(quantifier example) → OL-ONLY: pedagogical example with ∀ and ∃
- **Role**: APPLY
- **Variant Tags**: prfAX, FOL
- **Dual ID**: FOL=fol/axd/prq
- **Compression Signal**: PEDAGOGICAL (teaching by example)
- **Ped. Prerequisites**: fol/axd/pro, fol/axd/qua
- **OL Cross-refs**: olref[prp]{ax:*}, olref[qua]{ax:*}, olref[pro]{prop:chain}
- **Notes**: Example derivation using quantifier rules and axioms. Shows how to apply QR with eigenvariable condition.

---

# NATURAL DEDUCTION CHAPTER


### Chapter: natural-deduction

### fol/ntd/rul — Rules and Derivation
- **File**: content/first-order-logic/natural-deduction/rules-and-proofs.tex
- **Domain**: DED
- **Introduces**: PRIM-DED009 (Assumption Discharge), DEF-DED006 (Natural Deduction System)
- **References**: PRIM-DED003 (Rule of Inference), PRIM-SYN003 (Logical Connective), PRIM-SYN013 (Sentence)
- **OL Formal Items**:
  - defn(Assumption) → OL-ONLY: top-level sentence
- **Role**: DEFINE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/rul, PL=pl/ntd/rul
- **Compression Signal**: CORE-DEF (foundational definition for ND)
- **Ped. Prerequisites**: (none, chapter introduction)
- **OL Cross-refs**: (none)
- **Notes**: Introduces tree-structured derivations with assumption discharge. Intro/Elim pattern for each connective.

---


### fol/ntd/der — Derivations
- **File**: content/first-order-logic/natural-deduction/derivations.tex
- **Domain**: DED
- **Introduces**: PRIM-DED005 (Derivation - ND version), PRIM-DED006 (Provability - ND version)
- **References**: PRIM-DED009 (Assumption Discharge), DEF-DED006 (Natural Deduction System)
- **OL Formal Items**:
  - defn(Derivation) → PRIM-DED005: tree-structured derivation
  - ex(multiple examples) → OL-ONLY: pedagogical examples
- **Role**: DEFINE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/der, PL=pl/ntd/der
- **Compression Signal**: CORE-DEF (formal definition)
- **Ped. Prerequisites**: fol/ntd/rul
- **OL Cross-refs**: (none)
- **Notes**: Defines derivation as tree where bottom is conclusion, top are assumptions, and each step follows by a rule. Introduces Γ⊢A notation.

---


### fol/ntd/ppr — Derivability and Propositional Connectives
- **File**: content/first-order-logic/natural-deduction/provability-propositional.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), PRIM-SYN003 (Logical Connective), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - prop(provability-land) → OL-ONLY: conjunction properties
  - prop(provability-lor) → OL-ONLY: disjunction properties
  - prop(provability-lif) → OL-ONLY: implication properties
- **Role**: PROVE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/ppr, PL=pl/ntd/ppr
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/ntd/der, fol/ntd/prl
- **OL Cross-refs**: (none)
- **Notes**: Establishes same facts as axiomatic version but using ND rules. Dual structure.

---


### fol/ntd/qpr — Derivability and Quantifiers
- **File**: content/first-order-logic/natural-deduction/provability-quantifiers.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), PRIM-SYN004 (Quantifier)
- **OL Formal Items**:
  - thm(strong-generalization) → OL-ONLY: strong generalization
  - prop(provability-quantifiers) → OL-ONLY: quantifier instantiation/introduction
- **Role**: PROVE
- **Variant Tags**: prfND, FOL
- **Dual ID**: FOL=fol/ntd/qpr
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/ntd/der, fol/ntd/qrl
- **OL Cross-refs**: (none)
- **Notes**: ND analog of axiomatic quantifier properties. Uses eigenvariable condition from ∀-Intro and ∃-Elim.

---


### fol/ntd/ptn — Proof-Theoretic Notions
- **File**: content/first-order-logic/natural-deduction/proof-theoretic-notions.tex
- **Domain**: DED
- **Introduces**: PRIM-DED010 (Theorem - ND version), PRIM-DED006 (Provability - ND version), DEF-DED001 (Syntactic Consistency - ND version)
- **References**: PRIM-SEM009 (Validity), PRIM-SEM010 (Logical Consequence)
- **OL Formal Items**:
  - defn(Theorems) → PRIM-DED010: Theorem
  - defn(Derivability) → PRIM-DED006: Provability
  - defn(Consistency) → DEF-DED001: Syntactic Consistency
  - prop(reflexivity, monotonicity, transitivity) → OL-ONLY: structural properties
  - prop(incons) → OL-ONLY: inconsistency characterization
  - prop(proves-compact) → OL-ONLY: compactness
- **Role**: DEFINE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/ptn, PL=pl/ntd/ptn
- **Compression Signal**: CORE-DEF (foundational proof-theoretic concepts)
- **Ped. Prerequisites**: fol/ntd/der
- **OL Cross-refs**: (none)
- **Notes**: Exact parallel to axiomatic version. Same structural properties but for ND system.

---


### fol/ntd/sou — Soundness
- **File**: content/first-order-logic/natural-deduction/soundness.tex
- **Domain**: DED
- **Introduces**: CP-001 (Soundness — ND variant)
- **References**: PRIM-DED006 (Provability), PRIM-SEM009 (Validity), PRIM-SEM010 (Logical Consequence), PRIM-SEM007 (Satisfaction), DEF-DED001 (Syntactic Consistency), DEF-DED006 (Natural Deduction)
- **OL Formal Items**:
  - thm(soundness) → CP-001: soundness for natural deduction (Γ⊢φ → Γ⊨φ)
  - cor(weak-soundness) → OL-ONLY: corollary of CP-001
  - cor(consistency-soundness) → OL-ONLY: corollary of CP-001
- **Role**: PROVE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/sou, PL=pl/ntd/sou
- **Compression Signal**: CORE-THM (soundness metatheorem)
- **Ped. Prerequisites**: fol/ntd/der, fol/ntd/ptn, semantics chapter
- **OL Cross-refs**: olref[syn][ext]{prop:*}, olref[syn][sem]{thm:sem-deduction}
- **Notes**: Proof by induction on derivation. Large case analysis (one case per rule). Dual with axiomatic soundness.

---


### fol/ntd/ide — Derivation with Identity
- **File**: content/first-order-logic/natural-deduction/identity.tex
- **Domain**: DED
- **Introduces**: (none, extends system)
- **References**: PRIM-DED003 (Rule of Inference), DEF-DED006 (Natural Deduction System)
- **OL Formal Items**:
  - (rules displayed) → OL-ONLY: identity rules (∃I and ∃E)
  - ex(multiple examples) → OL-ONLY: pedagogical examples
- **Role**: APPLY
- **Variant Tags**: prfND, FOL
- **Dual ID**: FOL=fol/ntd/ide
- **Compression Signal**: PEDAGOGICAL (extension to system)
- **Ped. Prerequisites**: fol/ntd/der
- **OL Cross-refs**: (none)
- **Notes**: Adds ∃-Intro (no premises, derives t=t) and ∃-Elim (Leibniz Law). Simple extension pattern.

---


### fol/ntd/pro — Examples of Derivation
- **File**: content/first-order-logic/natural-deduction/proving-things.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED005 (Derivation), PRIM-DED009 (Assumption Discharge), DEF-DED006 (Natural Deduction System)
- **OL Formal Items**:
  - ex(multiple examples) → OL-ONLY: pedagogical examples
- **Role**: APPLY
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/pro, PL=pl/ntd/pro
- **Compression Signal**: PEDAGOGICAL (teaching by example)
- **Ped. Prerequisites**: fol/ntd/der, fol/ntd/prl
- **OL Cross-refs**: (none)
- **Notes**: Extensive examples showing ND proof strategies: work backward from conclusion, apply intro rules, discharge assumptions. Shows FalseCl usage.

---


### fol/ntd/prq — Derivation with Quantifiers
- **File**: content/first-order-logic/natural-deduction/proving-things-quant.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED005 (Derivation), PRIM-SYN004 (Quantifier), PRIM-DED009 (Assumption Discharge)
- **OL Formal Items**:
  - ex(multiple examples) → OL-ONLY: pedagogical examples
- **Role**: APPLY
- **Variant Tags**: prfND, FOL
- **Dual ID**: FOL=fol/ntd/prq
- **Compression Signal**: PEDAGOGICAL (teaching by example)
- **Ped. Prerequisites**: fol/ntd/pro, fol/ntd/qrl
- **OL Cross-refs**: (none)
- **Notes**: Examples showing quantifier reasoning in ND. Emphasizes eigenvariable condition management.

---


### fol/ntd/prv — Derivability and Consistency
- **File**: content/first-order-logic/natural-deduction/provability-consistency.tex
- **Domain**: DED
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), DEF-DED001 (Syntactic Consistency), PRIM-DED009 (Assumption Discharge)
- **OL Formal Items**:
  - prop(provability-contr) → OL-ONLY: contradiction property
  - prop(prov-incons) → OL-ONLY: derivability iff inconsistency of negation
  - prop(explicit-inc) → OL-ONLY: explicit inconsistency
  - prop(provability-exhaustive) → OL-ONLY: exhaustion principle
- **Role**: PROVE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/prv, PL=pl/ntd/prv
- **Compression Signal**: STEPPING-STONE (needed for completeness)
- **Ped. Prerequisites**: fol/ntd/ptn
- **OL Cross-refs**: olref[ptn]{prop:*}
- **Notes**: Same properties as axiomatic version but proved using ND techniques. Dual structure.

---


### fol/ntd/prl — Propositional Rules
- **File**: content/first-order-logic/natural-deduction/propositional-rules.tex
- **Domain**: DED
- **Introduces**: DEF-DED006 (Natural Deduction System - propositional part), PRIM-DED003 (Rule of Inference - ND version), PRIM-DED009 (Assumption Discharge)
- **References**: PRIM-SYN003 (Logical Connective)
- **OL Formal Items**:
  - (rules displayed for ∧, ∨, →, ¬, ⊥) → DEF-DED006: Introduction and Elimination rules
- **Role**: DEFINE
- **Variant Tags**: prfND, FOL/PL
- **Dual ID**: FOL=fol/ntd/prl, PL=pl/ntd/prl
- **Compression Signal**: CORE-DEF (defines the ND system)
- **Ped. Prerequisites**: fol/ntd/rul
- **OL Cross-refs**: (none)
- **Notes**: Specifies all propositional rules in intro/elim pairs. Includes FalseInt and FalseCl.

---


### fol/ntd/qrl — Quantifier Rules
- **File**: content/first-order-logic/natural-deduction/quantifier-rules.tex
- **Domain**: DED
- **Introduces**: DEF-DED006 (Natural Deduction System - quantifier part), PRIM-DED003 (Rule of Inference - quantifier version), PRIM-DED007 (Structural Rule - eigenvariable condition)
- **References**: PRIM-SYN004 (Quantifier)
- **OL Formal Items**:
  - (rules displayed for ∀, ∃) → DEF-DED006: Introduction and Elimination rules
  - (eigenvariable condition) → PRIM-DED007: Structural Rule
- **Role**: DEFINE
- **Variant Tags**: prfND, FOL
- **Dual ID**: FOL=fol/ntd/qrl
- **Compression Signal**: CORE-DEF (extends system to FOL)
- **Ped. Prerequisites**: fol/ntd/prl
- **OL Cross-refs**: (none)
- **Notes**: Specifies quantifier rules with eigenvariable conditions. Explains why eigenvariable condition is necessary for soundness.

---


### fol/ntd/sid — Soundness with Identity
- **File**: content/first-order-logic/natural-deduction/soundness-identity.tex
- **Domain**: DED
- **Introduces**: (none, extends theorem)
- **References**: PRIM-DED006 (Provability), PRIM-SEM007 (Satisfaction)
- **OL Formal Items**:
  - prop(ND with identity is sound) → OL-ONLY: extension of soundness theorem
- **Role**: PROVE
- **Variant Tags**: prfND, FOL
- **Dual ID**: FOL=fol/ntd/sid
- **Compression Signal**: STEPPING-STONE (extends soundness)
- **Ped. Prerequisites**: fol/ntd/sou, fol/ntd/ide
- **OL Cross-refs**: olref[fol][syn][ext]{prop:ext-formulas}
- **Notes**: Extends soundness proof to handle identity rules. Additional cases for ∃-Intro and ∃-Elim.

---

# SUMMARY STATISTICS

## Taxonomy Coverage
- **Introduced primitives**: 7 (DED001, DED003, DED005, DED006, DED007, DED009, DED010)
- **Introduced axioms**: 3 (DED001, DED002, DED003)
- **Introduced definitions**: 6 (DED001, DED002, DED005, DED006)
- **Introduced theorems**: 1 (DED001)
- **Referenced from other domains**: SYN (4), SEM (4), BST (2)
- **OL-ONLY items**: ~60+ (structural properties, specific derivability facts, pedagogical examples)

## Dual Structure
- **8 dual FOL/PL pairs**: rul, prv, ptn, ppr, ded, sou, pro, prv (both systems)
- **7 FOL-only sections**: qpr, qua, ddq, prq, ide, qrl, sid, prq (quantifier-specific)
- **Nearly identical content**: ptn, ppr, sou, prv (consistency properties)

## Role Distribution
- **DEFINE**: 7 sections (axiom/rule specs, basic definitions)
- **PROVE**: 11 sections (metatheorems, technical properties)
- **APPLY**: 5 sections (examples, pedagogical)
- **DISCUSS**: 0

## Compression Opportunities
- **CORE-DEF**: 5 (foundational system specifications)
- **CORE-THM**: 3 (Deduction Theorem, Soundness)
- **STEPPING-STONE**: 11 (technical lemmas for completeness)
- **PEDAGOGICAL**: 6 (examples and applications)
- **REDUNDANT**: 0 (but dual structures suggest consolidation potential)

## Key Insights
1. **Dual proof systems**: Two completely parallel developments (AXD and NTD) prove same metatheorems
2. **Shared structure**: Both have same proof-theoretic notions (ptn), consistency properties (prv), soundness theorems
3. **System-specific**: Rule specifications differ (Hilbert axioms vs. intro/elim rules)
4. **FOL extension pattern**: Both extend naturally from PL to FOL via quantifier sections
5. **Completeness infrastructure**: Large portion (11 sections) builds technical machinery for completeness proof
6. **Pedagogical duplication**: Each system has examples (pro, prq) showing how to construct derivations

## Consolidation Potential
- **Merge proof-theoretic notions**: Single abstract treatment of Γ⊢φ, consistency, structural properties (reflexivity, monotonicity, transitivity, compactness)
- **Unify metatheorems**: Single soundness proof parameterized by system; single statement of Deduction Theorem
- **Abstract rule interface**: Specify what properties a proof system must have, then show both AXD and NTD satisfy them
- **Consolidate examples**: One set of pedagogical examples showing proofs in both systems

This mapping reveals that the OpenLogic treatment is pedagogically thorough but taxonomically redundant. A lean systematization would define:
1. Abstract proof system interface (PRIM-DED004)
2. Single soundness theorem (parameterized)
3. Single completeness theorem (parameterized)
4. Two instantiations: Hilbert-style and Natural Deduction
### Chapter: sequent-calculus

### fol/seq/rul — Rules and Derivations
- **File**: content/first-order-logic/sequent-calculus/rules-and-proofs.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/rul, PL=pl/seq/rul
- **Introduces**: DEF-DED007 (Sequent Calculus), PRIM-DED008 (Sequent), PRIM-DED004 (Proof System - LK)
- **References**: (none - foundational)
- **OL Formal Items**:
  - defn[Sequent] → PRIM-DED008
  - defn[Initial Sequent] → axiom for PRIM-DED004
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: Syntax chapter (formulas)
- **OL Cross-refs**: (defines foundational concepts)
- **Notes**: Introduces sequent notation Γ⇒Δ and initial sequents; foundational for LK system


### fol/seq/prl — Propositional Rules
- **File**: content/first-order-logic/sequent-calculus/propositional-rules.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/prl, PL=pl/seq/prl
- **Introduces**: PRIM-DED003 (Rules of Inference - propositional instances)
- **References**: PRIM-DED008, PRIM-DED004
- **OL Formal Items**:
  - defish[¬L, ¬R] → OL-ONLY: propositional rule instances
  - defish[∧L, ∧R] → OL-ONLY: propositional rule instances
  - defish[∨L, ∨R] → OL-ONLY: propositional rule instances
  - defish[→L, →R] → OL-ONLY: propositional rule instances
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/rul
- **OL Cross-refs**: (none)
- **Notes**: Defines logical rules for propositional connectives in LK


### fol/seq/srl — Structural Rules
- **File**: content/first-order-logic/sequent-calculus/structural-rules.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/srl, PL=pl/seq/srl
- **Introduces**: PRIM-DED007 (Structural Rules), CP-010 (Cut Elimination — stated informally, cut described as admissible)
- **References**: PRIM-DED008, PRIM-DED004
- **OL Formal Items**:
  - defish[Weakening-L, Weakening-R] → PRIM-DED007 instances
  - defish[Contraction-L, Contraction-R] → PRIM-DED007 instances
  - defish[Exchange-L, Exchange-R] → PRIM-DED007 instances
  - defish[Cut] → CP-010: cut rule (described as admissible — THM-DED003)
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/prl
- **OL Cross-refs**: (mentions Cut as convenience, not necessity)
- **Notes**: Introduces structural rules. Cut mentioned as admissible but NOT formally proved (no Hauptsatz proof in OL). CP-010/THM-DED003 coverage is PARTIAL — the statement is given informally but the proof is absent.


### fol/seq/qrl — Quantifier Rules
- **File**: content/first-order-logic/sequent-calculus/quantifier-rules.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/qrl, PL=(none - FOL only)
- **Introduces**: PRIM-DED003 (Rules for quantifiers)
- **References**: PRIM-DED008, PRIM-DED004
- **OL Formal Items**:
  - defish[∀L, ∀R] → OL-ONLY: quantifier rule instances
  - defish[∃L, ∃R] → OL-ONLY: quantifier rule instances
  - explain[eigenvariable condition] → OL-ONLY: technical constraint
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/srl
- **OL Cross-refs**: (references syntax section for substitution)
- **Notes**: Defines quantifier rules with eigenvariable conditions; FOL-specific


### fol/seq/der — Derivations
- **File**: content/first-order-logic/sequent-calculus/derivations.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/der, PL=pl/seq/der
- **Introduces**: PRIM-DED005 (Derivation in LK)
- **References**: PRIM-DED008, PRIM-DED004, PRIM-DED003, PRIM-DED007
- **OL Formal Items**:
  - defn[LK-derivation] → PRIM-DED005
  - ex → OL-ONLY: pedagogical examples
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/qrl
- **OL Cross-refs**: (none)
- **Notes**: Defines derivations as trees of sequents; includes worked examples


### fol/seq/pro — Examples of Derivations
- **File**: content/first-order-logic/sequent-calculus/proving-things.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/pro, PL=pl/seq/pro
- **Introduces**: (none)
- **References**: PRIM-DED005, PRIM-DED008
- **OL Formal Items**:
  - ex (multiple) → OL-ONLY: pedagogical examples
  - prob (multiple) → OL-ONLY: exercises
- **Role**: APPLY
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/seq/der
- **OL Cross-refs**: (extensive worked examples)
- **Notes**: Propositional derivation examples; pedagogical scaffolding; could be condensed


### fol/seq/prq — Derivations with Quantifiers
- **File**: content/first-order-logic/sequent-calculus/proving-things-quant.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/prq, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED005, PRIM-DED003 (quantifier rules)
- **OL Formal Items**:
  - ex (multiple) → OL-ONLY: pedagogical examples with quantifiers
  - prob (multiple) → OL-ONLY: exercises
- **Role**: APPLY
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/seq/pro, fol/seq/qrl
- **OL Cross-refs**: (worked examples with eigenvariable conditions)
- **Notes**: FOL-specific examples; shows eigenvariable constraint application


### fol/seq/ptn — Proof-Theoretic Notions
- **File**: content/first-order-logic/sequent-calculus/proof-theoretic-notions.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/ptn, PL=pl/seq/ptn
- **Introduces**: PRIM-DED006 (Provability), PRIM-DED010 (Theorem), DEF-DED001 (Consistency), DEF-DED003 (Deductive Closure)
- **References**: PRIM-DED005
- **OL Formal Items**:
  - defn[Theorems] → PRIM-DED010
  - defn[derivability] → PRIM-DED006
  - defn[Consistency] → DEF-DED001
  - prop[Reflexivity] → OL-ONLY: basic property
  - prop[Monotonicity] → OL-ONLY: basic property
  - prop[Transitivity] → OL-ONLY: basic property
  - prop[incons] → OL-ONLY: characterization
  - prop[Compactness] → OL-ONLY: provability compactness
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/der
- **OL Cross-refs**: (cross-system definitions)
- **Notes**: Defines key proof-theoretic concepts; establishes Γ⊢φ notation


### fol/seq/prv — Derivability and Consistency
- **File**: content/first-order-logic/sequent-calculus/provability-consistency.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/prv, PL=pl/seq/prv
- **Introduces**: (none)
- **References**: PRIM-DED006, DEF-DED001
- **OL Formal Items**:
  - prop[provability-contr] → OL-ONLY: technical lemma
  - prop[prov-incons] → OL-ONLY: provability/inconsistency link
  - prop[explicit-inc] → OL-ONLY: inconsistency criterion
  - prop[provability-exhaustive] → OL-ONLY: case exhaustion
- **Role**: PROVE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/seq/ptn
- **OL Cross-refs**: (uses Cut rule extensively)
- **Notes**: Proves properties needed for completeness proof; technical lemmas


### fol/seq/ppr — Derivability and Propositional Connectives
- **File**: content/first-order-logic/sequent-calculus/provability-propositional.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/ppr, PL=pl/seq/ppr
- **Introduces**: (none)
- **References**: PRIM-DED006, AX-DED001 (establishes modus ponens property)
- **OL Formal Items**:
  - prop[provability-land] → OL-ONLY: conjunction properties
  - prop[provability-lor] → OL-ONLY: disjunction properties
  - prop[provability-lif] → OL-ONLY: implication properties (includes modus ponens)
- **Role**: PROVE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/seq/ptn
- **OL Cross-refs**: (for completeness proof)
- **Notes**: Establishes derivability facts for connectives; modus ponens as derived


### fol/seq/qpr — Derivability and Quantifiers
- **File**: content/first-order-logic/sequent-calculus/provability-quantifiers.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/qpr, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED006, AX-DED002 (related to universal generalization)
- **OL Formal Items**:
  - thm[strong-generalization] → relates to AX-DED002
  - prop[provability-quantifiers] → OL-ONLY: quantifier instantiation/generalization
- **Role**: PROVE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/seq/ppr
- **OL Cross-refs**: (for completeness proof)
- **Notes**: Establishes quantifier derivability properties; eigenvariable handling


### fol/seq/sou — Soundness
- **File**: content/first-order-logic/sequent-calculus/soundness.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/sou, PL=pl/seq/sou
- **Introduces**: CP-001 (Soundness — sequent calculus variant)
- **References**: PRIM-DED005, PRIM-DED006, DEF-DED007 (Sequent Calculus)
- **OL Formal Items**:
  - defn[valid sequent] → OL-ONLY: semantic notion for sequents
  - thm[sequent-soundness] → CP-001: soundness for sequent calculus
  - cor[weak-soundness] → OL-ONLY: corollary of CP-001
  - cor[entailment-soundness] → OL-ONLY: corollary of CP-001
  - cor[consistency-soundness] → OL-ONLY: corollary of CP-001
- **Role**: PROVE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/seq/qpr, semantics chapter
- **OL Cross-refs**: extensive references to syntax/semantics
- **Notes**: Proves LK soundness by induction on derivation structure; foundational metatheorem


### fol/seq/ide — Derivations with Identity
- **File**: content/first-order-logic/sequent-calculus/identity.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/ide, PL=(none - FOL only)
- **Introduces**: PRIM-DED003 (identity rules)
- **References**: PRIM-DED008, PRIM-DED004
- **OL Formal Items**:
  - defn[Initial sequents for =] → extension to PRIM-DED004
  - defish[= rules] → PRIM-DED003 instances
  - ex[Leibniz's Law, symmetry, transitivity] → OL-ONLY: identity properties
- **Role**: DEFINE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/seq/qrl
- **OL Cross-refs**: (identity chapter in semantics)
- **Notes**: Extends LK with identity; proves basic identity properties


### fol/seq/sid — Soundness with Identity
- **File**: content/first-order-logic/sequent-calculus/soundness-identity.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/seq/sid, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED003 (identity rules), PRIM-DED005
- **OL Formal Items**:
  - prop[soundness with identity] → OL-ONLY: extended soundness
- **Role**: PROVE
- **Variant Tags**: FOL, prfLK
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/seq/sou, fol/seq/ide
- **OL Cross-refs**: syntax/semantics for identity
- **Notes**: Extends soundness proof to identity rules


### fol/tab/ptn — Proof-Theoretic Notions
- **File**: content/first-order-logic/tableaux/proof-theoretic-notions.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/ptn, PL=pl/tab/ptn
- **Introduces**: PRIM-DED006 (Provability - tableau version), PRIM-DED010 (Theorem - tableau version), DEF-DED001 (Consistency - tableau version)
- **References**: PRIM-DED005
- **OL Formal Items**:
  - defn[Theorems] → PRIM-DED010 (tableau version)
  - defn[derivability] → PRIM-DED006 (tableau version)
  - defn[Consistency] → DEF-DED001 (tableau version)
  - prop[Reflexivity, Monotonicity, Transitivity] → OL-ONLY: basic properties
  - prop[incons] → OL-ONLY: characterization
  - prop[Compactness] → OL-ONLY: provability compactness
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF (REDUNDANT-WITH: fol/seq/ptn for cross-system)
- **Ped. Prerequisites**: fol/tab/der
- **OL Cross-refs**: (parallel to sequent calculus definitions)
- **Notes**: Parallel definitions to seq/ptn; demonstrates same concepts in tableau framework


### fol/tab/prv — Derivability and Consistency
- **File**: content/first-order-logic/tableaux/provability-consistency.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/prv, PL=pl/tab/prv
- **Introduces**: (none)
- **References**: PRIM-DED006, DEF-DED001
- **OL Formal Items**:
  - prop[provability-contr] → OL-ONLY: technical lemma (tableau version)
  - prop[prov-incons] → OL-ONLY: provability/inconsistency link
  - prop[explicit-inc] → OL-ONLY: inconsistency criterion
  - prop[provability-exhaustive] → OL-ONLY: case exhaustion
- **Role**: PROVE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: STEPPING-STONE (REDUNDANT-WITH: fol/seq/prv for results)
- **Ped. Prerequisites**: fol/tab/ptn
- **OL Cross-refs**: (uses Cut rule for constructions)
- **Notes**: Parallel proofs to seq/prv; same results, different proof structure


### fol/tab/ppr — Derivability and Propositional Connectives
- **File**: content/first-order-logic/tableaux/provability-propositional.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/ppr, PL=pl/tab/ppr
- **Introduces**: (none)
- **References**: PRIM-DED006
- **OL Formal Items**:
  - prop[provability-land] → OL-ONLY: conjunction properties (tableau version)
  - prop[provability-lor] → OL-ONLY: disjunction properties
  - prop[provability-lif] → OL-ONLY: implication properties
- **Role**: PROVE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: STEPPING-STONE (REDUNDANT-WITH: fol/seq/ppr)
- **Ped. Prerequisites**: fol/tab/ptn
- **OL Cross-refs**: (for completeness proof)
- **Notes**: Same results as seq/ppr, tableau-specific proofs


### fol/tab/qpr — Derivability and Quantifiers
- **File**: content/first-order-logic/tableaux/provability-quantifiers.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/qpr, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED006
- **OL Formal Items**:
  - thm[strong-generalization] → OL-ONLY: generalization (tableau version)
  - prop[provability-quantifiers] → OL-ONLY: quantifier properties
- **Role**: PROVE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: STEPPING-STONE (REDUNDANT-WITH: fol/seq/qpr)
- **Ped. Prerequisites**: fol/tab/ppr
- **OL Cross-refs**: (for completeness proof)
- **Notes**: Parallel to seq/qpr; tableau-specific proof techniques


### fol/tab/sou — Soundness
- **File**: content/first-order-logic/tableaux/soundness.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/sou, PL=pl/tab/sou
- **Introduces**: CP-001 (Soundness — tableau variant)
- **References**: PRIM-DED005, PRIM-DED006, DEF-DED008 (Tableau System)
- **OL Formal Items**:
  - defn[satisfies signed formula] → OL-ONLY: semantic notion for tableaux
  - thm[tableau-soundness] → CP-001: soundness for tableaux
  - cor[weak-soundness, entailment-soundness, consistency-soundness] → OL-ONLY: corollaries of CP-001
- **Role**: PROVE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-THM (REDUNDANT-WITH: fol/seq/sou for result)
- **Ped. Prerequisites**: fol/tab/qpr, semantics chapter
- **OL Cross-refs**: extensive references to syntax/semantics
- **Notes**: Proves tableau soundness; different proof strategy than sequent calculus (branch satisfaction)


### fol/tab/ide — Tableaux with Identity
- **File**: content/first-order-logic/tableaux/identity.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/ide, PL=(none - FOL only)
- **Introduces**: PRIM-DED003 (identity rules - tableau version)
- **References**: PRIM-DED004, PRIM-DED005
- **OL Formal Items**:
  - defish[= rule, T=, F=] → PRIM-DED003 instances (tableau-specific)
  - ex[Leibniz's Law, symmetry, transitivity] → OL-ONLY: identity properties
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF (REDUNDANT-WITH: fol/seq/ide for concepts)
- **Ped. Prerequisites**: fol/tab/qrl
- **OL Cross-refs**: (identity semantics)
- **Notes**: Tableau identity rules; slightly different formulation than LK


### fol/tab/sid — Soundness with Identity
- **File**: content/first-order-logic/tableaux/soundness-identity.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/sid, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED003 (identity rules), PRIM-DED005
- **OL Formal Items**:
  - prop[soundness with identity] → OL-ONLY: extended soundness
- **Role**: PROVE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: STEPPING-STONE (REDUNDANT-WITH: fol/seq/sid)
- **Ped. Prerequisites**: fol/tab/sou, fol/tab/ide
- **OL Cross-refs**: syntax/semantics for identity
- **Notes**: Extends tableau soundness to identity; parallel to seq/sid


### Chapter: tableaux

### fol/tab/rul — Rules and Tableaux
- **File**: content/first-order-logic/tableaux/rules-and-proofs.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/rul, PL=pl/tab/rul
- **Introduces**: DEF-DED008 (Tableau System), PRIM-DED004 (Proof System - Tableaux), PRIM-DED005 (Tableau derivation)
- **References**: (none - foundational)
- **OL Formal Items**:
  - defn[signed formula] → OL-ONLY: tableau-specific notion
  - explain[closed tableau] → OL-ONLY: tableau closure
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: Syntax chapter
- **OL Cross-refs**: (defines tableau basics)
- **Notes**: Introduces signed formulas T:A, F:A; tree structure for tableaux


### fol/tab/prl — Propositional Rules
- **File**: content/first-order-logic/tableaux/propositional-rules.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/prl, PL=pl/tab/prl
- **Introduces**: PRIM-DED003 (Tableau rules - propositional)
- **References**: PRIM-DED004 (tableau system), PRIM-DED005
- **OL Formal Items**:
  - defish[T¬, F¬] → OL-ONLY: negation tableau rules
  - defish[T∧, F∧] → OL-ONLY: conjunction tableau rules
  - defish[T∨, F∨] → OL-ONLY: disjunction tableau rules
  - defish[T→, F→] → OL-ONLY: implication tableau rules
  - defish[Cut] → OL-ONLY: tableau cut rule (admissible)
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/tab/rul
- **OL Cross-refs**: (none)
- **Notes**: Defines propositional tableau rules; includes Cut (not necessary but convenient)


### fol/tab/qrl — Quantifier Rules
- **File**: content/first-order-logic/tableaux/quantifier-rules.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/qrl, PL=(none - FOL only)
- **Introduces**: PRIM-DED003 (Tableau rules - quantifiers)
- **References**: PRIM-DED004, PRIM-DED005
- **OL Formal Items**:
  - defish[T∀, F∀] → OL-ONLY: universal quantifier rules
  - defish[T∃, F∃] → OL-ONLY: existential quantifier rules
  - explain[eigenvariable condition] → OL-ONLY: tableau-specific constraint
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/tab/prl
- **OL Cross-refs**: (references substitution notation)
- **Notes**: Quantifier rules for tableaux; eigenvariable conditions parallel sequent calculus


### fol/tab/der — Tableaux
- **File**: content/first-order-logic/tableaux/derivations.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/der, PL=pl/tab/der
- **Introduces**: PRIM-DED005 (Tableau as derivation)
- **References**: PRIM-DED004, PRIM-DED003
- **OL Formal Items**:
  - defn[tableau] → PRIM-DED005 (tableau-specific)
  - ex → OL-ONLY: worked example
- **Role**: DEFINE
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: fol/tab/qrl
- **OL Cross-refs**: (none)
- **Notes**: Formalizes tableaux as trees of signed formulas with closure criterion


### fol/tab/pro — Examples of Tableaux
- **File**: content/first-order-logic/tableaux/proving-things.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/pro, PL=pl/tab/pro
- **Introduces**: (none)
- **References**: PRIM-DED005
- **OL Formal Items**:
  - ex (multiple) → OL-ONLY: pedagogical examples
  - prob (multiple) → OL-ONLY: exercises
- **Role**: APPLY
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/tab/der
- **OL Cross-refs**: (extensive worked examples)
- **Notes**: Propositional tableau examples; highly pedagogical; could be condensed


### fol/tab/prq — Tableaux with Quantifiers
- **File**: content/first-order-logic/tableaux/proving-things-quant.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/tab/prq, PL=(none - FOL only)
- **Introduces**: (none)
- **References**: PRIM-DED005, PRIM-DED003 (quantifier rules)
- **OL Formal Items**:
  - ex (multiple) → OL-ONLY: pedagogical examples with quantifiers
  - prob (multiple) → OL-ONLY: exercises
- **Role**: APPLY
- **Variant Tags**: FOL, prfTab
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/tab/pro, fol/tab/qrl
- **OL Cross-refs**: (demonstrates eigenvariable management)
- **Notes**: FOL-specific tableau examples; shows strategic rule application


### Chapter: proof-systems

### fol/prf/int — Introduction
- **File**: content/first-order-logic/proof-systems/introduction.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/prf/int, PL=pl/prf/int
- **Introduces**: (discusses meta-concepts)
- **References**: PRIM-DED004, PRIM-DED006, DEF-DED001
- **OL Formal Items**:
  - explain[derivation systems] → PRIM-DED004 (general discussion)
  - explain[soundness] → OL-ONLY: metatheoretic concept
  - explain[completeness] → OL-ONLY: metatheoretic concept
  - explain[consistency] → DEF-DED001 (general discussion)
- **Role**: DISCUSS
- **Variant Tags**: FOL
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: Semantics chapter
- **OL Cross-refs**: (cross-references all proof systems)
- **Notes**: Meta-level introduction; explains goals of derivation systems; connects syntax/semantics


### fol/prf/axd — Axiomatic Derivation
- **File**: content/first-order-logic/proof-systems/axiomatic-deduction.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/prf/axd, PL=pl/prf/axd
- **Introduces**: DEF-DED005 (Hilbert-Style Systems)
- **References**: PRIM-DED001, PRIM-DED003, AX-DED001, AX-DED003
- **OL Formal Items**:
  - explain[axiomatic system] → DEF-DED005
  - explain[axiom schemas] → PRIM-DED001, AX-DED003
  - explain[modus ponens] → AX-DED001
  - derivation example → OL-ONLY: illustration
- **Role**: DISCUSS
- **Variant Tags**: FOL
- **Compression Signal**: CORE-DEF (for Hilbert systems)
- **Ped. Prerequisites**: fol/prf/int
- **OL Cross-refs**: (references to Frege, Russell, Hilbert)
- **Notes**: Surveys axiomatic/Hilbert-style systems; maps to PRIM-DED001, AX-DED001, AX-DED003


### fol/prf/ntd — Natural Deduction
- **File**: content/first-order-logic/proof-systems/natural-deduction.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/prf/ntd, PL=pl/prf/ntd
- **Introduces**: DEF-DED006 (Natural Deduction System)
- **References**: PRIM-DED009 (Assumption Discharge), PRIM-DED003
- **OL Formal Items**:
  - explain[natural deduction] → DEF-DED006
  - explain[assumptions] → OL-ONLY: ND-specific notion
  - explain[discharge] → PRIM-DED009
  - explain[introduction/elimination rules] → PRIM-DED003 (ND instances)
  - derivation example → OL-ONLY: illustration
- **Role**: DISCUSS
- **Variant Tags**: FOL
- **Compression Signal**: CORE-DEF (for ND systems)
- **Ped. Prerequisites**: fol/prf/int
- **OL Cross-refs**: (references to Gentzen, Jaśkowski, Prawitz, Fitch)
- **Notes**: Surveys natural deduction; emphasizes PRIM-DED009; maps to DEF-DED006


### fol/prf/seq — The Sequent Calculus
- **File**: content/first-order-logic/proof-systems/sequent-calculus.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/prf/seq, PL=pl/prf/seq
- **Introduces**: (surveys existing)
- **References**: DEF-DED007, PRIM-DED008, PRIM-DED007
- **OL Formal Items**:
  - explain[sequent calculus] → DEF-DED007 (overview)
  - explain[sequents] → PRIM-DED008
  - explain[structural rules] → PRIM-DED007
  - derivation example → OL-ONLY: illustration
- **Role**: DISCUSS
- **Variant Tags**: FOL
- **Compression Signal**: PEDAGOGICAL (REDUNDANT-WITH: fol/seq chapter)
- **Ped. Prerequisites**: fol/prf/int
- **OL Cross-refs**: (references to Gentzen)
- **Notes**: Overview of sequent calculus; points to fol/seq for full treatment


### fol/prf/tab — Tableaux
- **File**: content/first-order-logic/proof-systems/tableaux.tex
- **Domain**: DED
- **Dual ID**: FOL=fol/prf/tab, PL=pl/prf/tab
- **Introduces**: (surveys existing)
- **References**: DEF-DED008, PRIM-DED005
- **OL Formal Items**:
  - explain[tableaux] → DEF-DED008 (overview)
  - explain[signed formulas] → OL-ONLY: tableau-specific
  - explain[closed tableau] → OL-ONLY: closure criterion
  - derivation example → OL-ONLY: illustration
- **Role**: DISCUSS
- **Variant Tags**: FOL
- **Compression Signal**: PEDAGOGICAL (REDUNDANT-WITH: fol/tab chapter)
- **Ped. Prerequisites**: fol/prf/int
- **OL Cross-refs**: (references to Beth, Hintikka, Smullyan)
- **Notes**: Overview of tableaux; points to fol/tab for full treatment; notes connection to sequent calculus



## Batch 5 — CMP (computability + turing-machines)


### Chapter: recursive-functions

### cmp/rec/int — Introduction
- **File**: content/computability/recursive-functions/introduction.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP001 Computable Function (discussed informally), DEF-CMP001 Partial Function (mentioned), DEF-CMP003 Characteristic Function (mentioned)
- **OL Formal Items**: (none - narrative introduction)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none - chapter opener)
- **OL Cross-refs**: (none)
- **Notes**: Motivates the chapter by explaining why number-theoretic functions are central to early computability theory; introduces primitive recursion, partial recursive functions, and general recursive functions informally.

---


### cmp/rec/pre — Primitive Recursion
- **File**: content/computability/recursive-functions/primitive-recursion.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP002 Primitive Recursive Function (conceptually introduced via pattern)
- **References**: PRIM-BST012 Natural Number, PRIM-BST009 Function
- **OL Formal Items**: (none - informal exposition)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/rec/int
- **OL Cross-refs**: (none)
- **Notes**: Explains the pattern of definition by primitive recursion through examples (exponentiation, addition, multiplication); establishes the recursive pattern $h(x,0) = f(x)$, $h(x,y+1) = g(x,y,h(x,y))$.

---


### cmp/rec/com — Composition
- **File**: content/computability/recursive-functions/composition.tex
- **Domain**: CMP
- **Introduces**: (none - composition is a building block)
- **References**: PRIM-CMP002 Primitive Recursive Function, PRIM-BST009 Function
- **OL Formal Items**: (none - informal exposition)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/rec/pre
- **OL Cross-refs**: (none)
- **Notes**: Defines composition of functions; introduces projection functions $\Proj{n}{i}$ which are essential for the formal definition of primitive recursive functions.

---


### cmp/rec/prf — Primitive Recursive Functions
- **File**: content/computability/recursive-functions/pr-functions.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP002 Primitive Recursive Function (formal definition)
- **References**: PRIM-BST012 Natural Number, PRIM-BST009 Function, PRIM-BST014 Inductive Definition
- **OL Formal Items**:
  - \begin{defn}[primitive-recursion] → PRIM-CMP002 (formal schema)
  - \begin{defn}[composition] → OL-ONLY: supporting definition
  - \begin{defn} (primitive recursive functions) → PRIM-CMP002 (inductive definition)
  - \begin{prop} (addition is PR) → OL-ONLY: example
  - \begin{prop}[mult-pr] (multiplication is PR) → OL-ONLY: example
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/rec/pre, cmp/rec/com
- **OL Cross-refs**: References to \olref{defn:primitive-recursion}
- **Notes**: Gives the complete inductive definition: base functions ($\Zero$, $\Succ$, projections), closed under composition and primitive recursion. Includes proofs that $\Add$ and $\Mult$ are primitive recursive.

---


### cmp/rec/not — Primitive Recursion Notations
- **File**: content/computability/recursive-functions/notation-pr-functions.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**: (none - notational system)
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/rec/prf
- **OL Cross-refs**: (none)
- **Notes**: Introduces a notation system ($\fn{Comp}_{k,n}$, $\fn{Rec}_k$) for systematically describing primitive recursive functions; useful for enumeration.

---


### cmp/rec/cmp — Primitive Recursive Functions are Computable
- **File**: content/computability/recursive-functions/pr-functions-computable.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**: (none - informal argument)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/rec/prf
- **OL Cross-refs**: (none)
- **Notes**: Argues informally that every primitive recursive function is computable by showing how to compute functions defined by composition and primitive recursion.

---


### cmp/rec/exa — Examples of Primitive Recursive Functions
- **File**: content/computability/recursive-functions/examples.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{prop} (exponentiation is PR) → OL-ONLY: example
  - \begin{prop} (predecessor is PR) → OL-ONLY: example
  - \begin{prop} (factorial is PR) → OL-ONLY: example
  - \begin{prop} (truncated subtraction is PR) → OL-ONLY: example
  - \begin{prop} (distance is PR) → OL-ONLY: example
  - \begin{prop} (maximum is PR) → OL-ONLY: example
  - \begin{prop}[min-pr] (minimum is PR) → OL-ONLY: example
  - \begin{prop} (closure under sums/products) → OL-ONLY: closure property
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/rec/prf
- **OL Cross-refs**: \olref[cmp][rec][exa]{prop:min-pr}
- **Notes**: Demonstrates that many familiar arithmetic functions (exp, pred, factorial, $\tsub$, max, min) are primitive recursive; also shows closure under finite sums and products.

---


### cmp/rec/prr — Primitive Recursive Relations
- **File**: content/computability/recursive-functions/pr-relations.tex
- **Domain**: CMP
- **Introduces**: DEF-CMP003 Characteristic Function ($\chi_R$ — formally defined here)
- **References**: DEF-CMP003 Characteristic Function, PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{defn} (PR relation) → OL-ONLY: definition via $\Char{R}$
  - \begin{prop} (closure under Boolean ops) → OL-ONLY: closure property
  - \begin{prop} (closure under bounded quantification) → OL-ONLY: closure property
  - \begin{prop} (definition by cases) → OL-ONLY: technical result
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/rec/exa
- **OL Cross-refs**: (none)
- **Notes**: Defines primitive recursive relations via characteristic functions; proves closure under Boolean operations and bounded quantification; introduces conditional function $\fn{cond}$.

---


### cmp/rec/bmi — Bounded Minimization
- **File**: content/computability/recursive-functions/bounded-minimization.tex
- **Domain**: CMP
- **Introduces**: (none - bounded minimization keeps us in PR)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{prop} (bounded minimization is PR) → OL-ONLY: closure property
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: cmp/rec/prr
- **OL Cross-refs**: (none)
- **Notes**: Shows that the operation $\bmin{z < y}{R(\vec{x}, z)}$ preserves primitive recursiveness; contrasts with unbounded minimization which does not.

---


### cmp/rec/pri — Primes
- **File**: content/computability/recursive-functions/primes.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**: (none - applications)
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/rec/bmi
- **OL Cross-refs**: (none)
- **Notes**: Shows that divisibility, primality, and the function $p_x$ (the $x$-th prime) are all primitive recursive; uses Euclid's theorem to bound the search.

---


### cmp/rec/seq — Sequences
- **File**: content/computability/recursive-functions/sequences.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP011 Gödel Numbering (sequences coded by numbers via prime factorization)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{prop} ($\len{s}$ is PR) → OL-ONLY: coding operation
  - \begin{prop} ($\fn{append}$ is PR) → OL-ONLY: coding operation
  - \begin{prop} ($\fn{element}$ is PR) → OL-ONLY: coding operation
  - \begin{prop} ($\fn{concat}$ is PR) → OL-ONLY: coding operation
  - \begin{prop}[subseq] ($\fn{subseq}$ is PR) → OL-ONLY: coding operation
- **Role**: APPLY
- **Compression Signal**: CORE-DEF (coding technique essential for later)
- **Ped. Prerequisites**: cmp/rec/pri
- **OL Cross-refs**: \olref[cmp][rec][seq]{prop:subseq}
- **Notes**: Develops coding of finite sequences via prime factorization $\tuple{a_0,\ldots,a_k} = p_0^{a_0+1} \cdots p_k^{a_k+1}$; shows operations on sequences are primitive recursive.

---


### cmp/rec/tre — Trees
- **File**: content/computability/recursive-functions/trees.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP002 Primitive Recursive Function, PRIM-CMP011 Gödel Numbering (for sequences)
- **OL Formal Items**:
  - \begin{prop}[subtreeseq] ($\fn{SubtreeSeq}$ is PR) → OL-ONLY: coding application
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/rec/seq
- **OL Cross-refs**: \olref[cmp][rec][tre]{prop:subtreeseq}
- **Notes**: Shows how to code trees as sequences; proves that operations on trees are primitive recursive.

---


### cmp/rec/ore — Other Recursions
- **File**: content/computability/recursive-functions/other-recursions.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**: (none - informal discussion)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/rec/tre
- **OL Cross-refs**: (none)
- **Notes**: Discusses variations: simultaneous recursion, course-of-values recursion; all can be simulated by ordinary primitive recursion using sequence coding.

---


### cmp/rec/npr — Non-Primitive Recursive Functions
- **File**: content/computability/recursive-functions/non-pr-functions.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP010 Diagonalization (used to show PR ⊊ computable)
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP002 Primitive Recursive Function, PRIM-CMP011 Gödel Numbering (for notations)
- **OL Formal Items**: (none - informal argument)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/rec/ore
- **OL Cross-refs**: (none)
- **Notes**: Uses diagonalization to show there exist computable functions (like Ackermann function) that are not primitive recursive; enumerates PR functions via codes.

---


### cmp/rec/par — Partial Recursive Functions
- **File**: content/computability/recursive-functions/partial-functions.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP003 μ-Recursion (unbounded search), PRIM-CMP001 Computable Function (partial & total recursive functions), DEF-CMP002 Total Function (recursive = total partial recursive)
- **References**: DEF-CMP001 Partial Function, PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{defn} (partial recursive functions) → PRIM-CMP003, PRIM-CMP001
  - \begin{defn}[recursive-fn] (recursive functions) → PRIM-CMP001 (total recursive = computable)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/rec/npr
- **OL Cross-refs**: \olref{defn:recursive-fn}
- **Notes**: Introduces unbounded minimization $\mu x \, f(x, \vec{z})$; defines partial recursive (= partial computable) and recursive (= computable) functions; explains partiality via undefined values.

---


### cmp/rec/nft — The Normal Form Theorem
- **File**: content/computability/recursive-functions/normal-form.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP011 Gödel Numbering (index $e$ for functions), DEF-CMP005 Index (Program), THM-CMP004 (Kleene Normal Form)
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP002 Primitive Recursive Function, PRIM-CMP003 μ-Recursion
- **OL Formal Items**:
  - \begin{thm}[kleene-nf] (Kleene's Normal Form Theorem) → THM-CMP004 (s-m-n implicit)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/rec/par
- **OL Cross-refs**: \olref{thm:kleene-nf}
- **Notes**: States (without full proof) that there exist primitive recursive $T(e,x,s)$ and $U(s)$ such that $f(x) \simeq U(\umin{s}{T(e,x,s)})$ for any partial recursive function; $T$ tests if $s$ codes a computation of function $e$ on input $x$.

---


### cmp/rec/hlt — The Halting Problem
- **File**: content/computability/recursive-functions/halting-problem.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP008 Halting Problem
- **References**: PRIM-CMP001 Computable Function, DEF-CMP005 Index, PRIM-CMP010 Diagonalization
- **OL Formal Items**:
  - \begin{thm}[halting-problem] (halting function not recursive) → THM-CMP002 Unsolvability of Halting Problem
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/rec/nft
- **OL Cross-refs**: \olref{thm:halting-problem}
- **Notes**: Proves that the halting function $h(e,x)$ (which decides if $\cfind{e}(x) \fdefined$) is not computable; uses diagonalization.

---


### cmp/rec/gen — General Recursive Functions
- **File**: content/computability/recursive-functions/general-recursive-functions.tex
- **Domain**: CMP
- **Introduces**: (none - alternative characterization)
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP003 μ-Recursion, DEF-CMP002 Total Function
- **OL Formal Items**:
  - \begin{defn}[general-recursive] (general recursive functions) → OL-ONLY: alternative definition
- **Role**: DEFINE
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: cmp/rec/par
- **OL Cross-refs**: \olref[par]{defn:recursive-fn}, \olref{defn:general-recursive}
- **Notes**: Defines general recursive functions (unbounded search only on regular functions); notes that general recursive = total recursive despite different-looking definitions.

---

## Chapter: Computability Theory (cmp/thy)


### Chapter: computability-theory

### cmp/thy/int — Introduction
- **File**: content/computability/computability-theory/introduction.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP012 Universal Turing Machine (as $\fn{Un}$), DEF-CMP004 Enumeration (of computable functions via $\cfind{k}$)
- **References**: PRIM-CMP001 Computable Function, DEF-CMP001 Partial Function, PRIM-CMP005 Church-Turing Thesis (informal appeal)
- **OL Formal Items**: (none - narrative introduction)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none - chapter opener)
- **OL Cross-refs**: (none)
- **Notes**: Introduces notation $\cfind{k}$ for the $k$-th partial computable function via universal function $\fn{Un}(k,x)$; discusses two proof strategies (rigorous via models vs. informal via Church's thesis).

---


### cmp/thy/cod — Coding Computations
- **File**: content/computability/computability-theory/coding-computations.tex
- **Domain**: CMP
- **Introduces**: (none - conceptual overview)
- **References**: PRIM-CMP011 Gödel Numbering (coding of definitions and computations), DEF-CMP005 Index
- **OL Formal Items**: (none - informal exposition)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/thy/int
- **OL Cross-refs**: (none)
- **Notes**: Explains conceptually that definitions of computable functions and their computation sequences can be coded as numbers; sets up for Normal Form Theorem.

---


### cmp/thy/nfm — The Normal Form Theorem
- **File**: content/computability/computability-theory/normal-form.tex
- **Domain**: CMP
- **Introduces**: (duplicate coverage of THM-CMP004)
- **References**: PRIM-CMP011 Gödel Numbering, DEF-CMP005 Index, PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{thm}[normal-form] (Kleene's Normal Form Theorem) → THM-CMP004 (duplicate from rec/nft)
  - \begin{thm} (infinitely many indices) → OL-ONLY: observation
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/cod
- **OL Cross-refs**: \olref{thm:normal-form}
- **Notes**: Sketch proof that $T$ and $U$ are primitive recursive; notes that $\cfind{e}(x) \simeq U(\umin{s}{T(e,x,s)})$ becomes the definition of $\cfind{e}$.

---


### cmp/thy/smn — The s-m-n Theorem
- **File**: content/computability/computability-theory/s-m-n.tex
- **Domain**: CMP
- **Introduces**: THM-CMP004 s-m-n Theorem
- **References**: PRIM-CMP002 Primitive Recursive Function, DEF-CMP005 Index
- **OL Formal Items**:
  - \begin{thm}[s-m-n] (s-m-n theorem) → THM-CMP004
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/nfm
- **OL Cross-refs**: \olref{thm:s-m-n}
- **Notes**: States (without proof) that there exist primitive recursive $s^m_n$ such that $\cfind{s^m_n(e,a_0,\ldots,a_{m-1})}[n](y_0,\ldots,y_{n-1}) \simeq \cfind{e}[m+n](a_0,\ldots,a_{m-1},y_0,\ldots,y_{n-1})$; allows "fixing arguments in programs."

---


### cmp/thy/uni — The Universal Partial Computable Function
- **File**: content/computability/computability-theory/universal-part-function.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP012 Universal Turing Machine (formally)
- **References**: THM-CMP004 (Normal Form)
- **OL Formal Items**:
  - \begin{thm}[univ-comp] (universal partial computable function) → PRIM-CMP012
- **Role**: PROVE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/thy/nfm
- **OL Cross-refs**: \olref[nfm]{thm:normal-form}
- **Notes**: Proves existence of universal partial computable function $\fn{Un}(e,x)$ using Normal Form; allows enumeration of all partial computable functions.

---


### cmp/thy/nou — No Universal Computable Function
- **File**: content/computability/computability-theory/no-universal-function.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP010 Diagonalization, PRIM-CMP012 Universal Turing Machine
- **OL Formal Items**:
  - \begin{thm}[no-univ] (no universal total function) → OL-ONLY: impossibility result
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/uni
- **OL Cross-refs**: \olref[uni]{thm:univ-comp}
- **Notes**: Proves by diagonalization that there is no total computable universal function; contrasts with existence of partial universal function.

---


### cmp/thy/hlt — The Halting Problem
- **File**: content/computability/computability-theory/halting-problem.tex
- **Domain**: CMP
- **Introduces**: (duplicate of PRIM-CMP008)
- **References**: PRIM-CMP012 Universal Turing Machine, PRIM-CMP010 Diagonalization
- **OL Formal Items**:
  - \begin{thm}[halting-problem] (halting problem undecidable) → THM-CMP002 (duplicate)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/nou
- **OL Cross-refs**: \olref[nou]{thm:no-univ}
- **Notes**: Two proofs that halting function $h(e,x)$ is not computable; includes Turing machine interpretation in tagblock.

---


### cmp/thy/rus — Comparison with Russell's Paradox
- **File**: content/computability/computability-theory/russells-paradox.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP010 Diagonalization
- **OL Formal Items**: (none - philosophical discussion)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/thy/hlt
- **OL Cross-refs**: (none)
- **Notes**: Contrasts Russell's paradox with diagonalization arguments in computability; clarifies partial vs. total, computable vs. noncomputable.

---


### cmp/thy/cps — Computable Sets
- **File**: content/computability/computability-theory/computable-sets.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP006 Decidable Set
- **References**: DEF-CMP003 Characteristic Function, PRIM-CMP001 Computable Function
- **OL Formal Items**:
  - \begin{defn} (computable set) → PRIM-CMP006
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/thy/rus
- **OL Cross-refs**: (none)
- **Notes**: Defines computable (decidable) sets as those with computable characteristic function.

---


### cmp/thy/ces — Computably Enumerable Sets
- **File**: content/computability/computability-theory/ce-sets.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP007 Semi-Decidable (c.e.) Set
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP006 Decidable Set
- **OL Formal Items**:
  - \begin{defn} (c.e. set) → PRIM-CMP007
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/thy/cps
- **OL Cross-refs**: (none)
- **Notes**: Defines computably enumerable (c.e.) sets as ranges of computable functions (or empty); shows computable ⇒ c.e.

---


### cmp/thy/eqc — Equivalent Definitions of C.E. Sets
- **File**: content/computability/computability-theory/equiv-ce-defs.tex
- **Domain**: CMP
- **Introduces**: DEF-CMP010 Recursive Enumerability (Equiv. Characterizations)
- **References**: PRIM-CMP007 Semi-Decidable (c.e.) Set, PRIM-CMP001 Computable Function, PRIM-CMP002 Primitive Recursive Function
- **OL Formal Items**:
  - \begin{thm}[ce-equiv] (c.e. characterizations) → DEF-CMP010
  - \begin{thm}[exists-char] (c.e. via $\exists$) → DEF-CMP010
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/ces
- **OL Cross-refs**: \olref{thm:ce-equiv}, \olref{case:ce}, etc.
- **Notes**: Proves equivalence of: (1) c.e., (2) range of partial computable, (3) range of PR (if nonempty), (4) domain of partial computable; introduces $W_e$ notation.

---


### cmp/thy/ncp — There Are Non-Computable Sets
- **File**: content/computability/computability-theory/non-comp-set.tex
- **Domain**: CMP
- **Introduces**: (none - $K_0$ and $K$ are specific examples)
- **References**: PRIM-CMP007 Semi-Decidable (c.e.) Set, PRIM-CMP006 Decidable Set, PRIM-CMP008 Halting Problem
- **OL Formal Items**:
  - \begin{thm}[K-0] ($K_0$ is c.e. but not computable) → OL-ONLY: key example
  - \begin{thm}[K] ($K$ is c.e. but not computable) → OL-ONLY: key example
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/eqc
- **OL Cross-refs**: \olref[hlt]{thm:halting-problem}
- **Notes**: Defines $K_0 = \{\tuple{e,x} : \cfind{e}(x) \fdefined\}$ and $K = \{e : \cfind{e}(e) \fdefined\}$ (halting/self-halting sets); proves both are c.e. but not computable.

---


### cmp/thy/clo — Union and Intersection of C.E. Sets
- **File**: content/computability/computability-theory/ce-closed-cup-cap.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP007 Semi-Decidable (c.e.) Set
- **OL Formal Items**:
  - \begin{thm} (c.e. closed under $\cup$, $\cap$) → OL-ONLY: closure property
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: cmp/thy/eqc
- **OL Cross-refs**: \olref[eqc]{thm:ce-equiv}
- **Notes**: Proves c.e. sets closed under union and intersection; gives multiple proofs using different characterizations of c.e.

---


### cmp/thy/cmp — Computably Enumerable Sets not Closed under Complement
- **File**: content/computability/computability-theory/complement-ce.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP007 Semi-Decidable (c.e.) Set, PRIM-CMP006 Decidable Set
- **OL Formal Items**:
  - \begin{thm}[ce-comp] (computable iff both $A$ and $\bar{A}$ c.e.) → OL-ONLY: characterization
  - \begin{cor}[comp-k] ($\bar{K_0}$ not c.e.) → OL-ONLY: consequence
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/clo
- **OL Cross-refs**: \olref[ncp]{thm:K-0}
- **Notes**: Proves $A$ computable iff both $A$ and $\bar{A}$ are c.e.; concludes $\bar{K_0}$ is not c.e.

---


### cmp/thy/red — Reducibility
- **File**: content/computability/computability-theory/reducibility.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP009 Many-One Reducibility
- **References**: PRIM-CMP001 Computable Function
- **OL Formal Items**:
  - \begin{defn} (many-one reduction) → PRIM-CMP009
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/thy/cmp
- **OL Cross-refs**: \olref[hlt]{thm:halting-problem}
- **Notes**: Defines many-one reducibility $A \leq_m B$ via computable $f$ such that $x \in A \iff f(x) \in B$; discusses one-one reducibility (stricter).

---


### cmp/thy/ppr — Properties of Reducibility
- **File**: content/computability/computability-theory/prop-reduce.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP009 Many-One Reducibility, PRIM-CMP007 Semi-Decidable (c.e.) Set, PRIM-CMP006 Decidable Set
- **OL Formal Items**:
  - \begin{prop}[trans-red] (transitivity of $\leq_m$) → OL-ONLY: property
  - \begin{prop}[reduce] ($A \leq_m B$ preserves c.e./decidable) → OL-ONLY: key property
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/red
- **OL Cross-refs**: \olref[cmp]{thm:ce-comp}
- **Notes**: Proves transitivity of $\leq_m$ and that if $A \leq_m B$ and $B$ is c.e. (or decidable), then so is $A$.

---


### cmp/thy/cce — Complete Computably Enumerable Sets
- **File**: content/computability/computability-theory/complete-ce-sets.tex
- **Domain**: CMP
- **Introduces**: DEF-CMP008 Creative Set (implicitly via completeness)
- **References**: PRIM-CMP009 Many-One Reducibility, PRIM-CMP007 Semi-Decidable (c.e.) Set
- **OL Formal Items**:
  - \begin{defn} (complete c.e. set) → DEF-CMP008 (related concept)
  - \begin{thm} ($K$, $K_0$, $K_1$ are complete c.e.) → OL-ONLY: key examples
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/ppr
- **OL Cross-refs**: \olref[k1]{prop:k1}, \olref[ppr]{prop:trans-red}
- **Notes**: Defines complete c.e. sets (hardest c.e. sets under $\leq_m$); shows $K$, $K_0$, $K_1$ are all complete.

---


### cmp/thy/k1 — An Example of Reducibility
- **File**: content/computability/computability-theory/k-1.tex
- **Domain**: CMP
- **Introduces**: (none - example application)
- **References**: PRIM-CMP009 Many-One Reducibility, THM-CMP004 s-m-n Theorem
- **OL Formal Items**:
  - \begin{prop}[k1] ($K_1$ is c.e. but not computable) → OL-ONLY: application
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/thy/smn
- **OL Cross-refs**: \olref[ppr]{prop:reduce}, \olref[eqc]{thm:exists-char}
- **Notes**: Defines $K_1 = \{e : \cfind{e}(0) \fdefined\}$; uses s-m-n to reduce $K_0$ to $K_1$, proving $K_1$ is c.e. but not computable.

---


### cmp/thy/tot — Totality is Undecidable
- **File**: content/computability/computability-theory/total.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: PRIM-CMP009 Many-One Reducibility, THM-CMP004 s-m-n Theorem, DEF-CMP002 Total Function
- **OL Formal Items**:
  - \begin{prop}[total] ($\fn{Tot}$ not computable) → OL-ONLY: undecidability result
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: cmp/thy/k1
- **OL Cross-refs**: (none)
- **Notes**: Defines $\fn{Tot} = \{x : \cfind{x} \text{ is total}\}$; uses s-m-n to reduce $K$ to $\fn{Tot}$, proving $\fn{Tot}$ is not computable (in fact not even c.e.).

---


### cmp/thy/rce — Rice's Theorem
- **File**: content/computability/computability-theory/rice-theorem.tex
- **Domain**: CMP
- **Introduces**: THM-CMP003 Rice's Theorem
- **References**: PRIM-CMP009 Many-One Reducibility, THM-CMP004 s-m-n Theorem
- **OL Formal Items**:
  - \begin{thm} (Rice's Theorem) → THM-CMP003
  - \begin{cor} (corollaries) → OL-ONLY: applications
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/tot
- **OL Cross-refs**: \olref[tot]{prop:total}
- **Notes**: Proves Rice's Theorem: no nontrivial index set (property of computable functions) is decidable; gives corollaries (totality, constancy, etc. all undecidable).

---


### cmp/thy/fix — The Fixed-Point Theorem
- **File**: content/computability/computability-theory/fixed-point-thm.tex
- **Domain**: CMP
- **Introduces**: THM-CMP005 Recursion Theorem (Kleene)
- **References**: THM-CMP004 s-m-n Theorem, PRIM-CMP012 Universal Turing Machine
- **OL Formal Items**:
  - \begin{lem}[fixed-equiv] (equivalent forms of fixed-point theorem) → THM-CMP005
  - \begin{thm} (fixed-point theorem) → THM-CMP005
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: cmp/thy/smn
- **OL Cross-refs**: \olref{lem:fixed-equiv}
- **Notes**: Proves Kleene's recursion/fixed-point theorem: for any partial computable $g(x,y)$, exists $e$ such that $\cfind{e}(y) \simeq g(e,y)$; allows self-reference in definitions.

---


### cmp/thy/apf — Applying the Fixed-Point Theorem
- **File**: content/computability/computability-theory/application-fixed-point.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: THM-CMP005 Recursion Theorem
- **OL Formal Items**:
  - \begin{thm} (no effective procedure for char. functions of decidable c.e. sets) → OL-ONLY: application
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/thy/fix
- **OL Cross-refs**: (none)
- **Notes**: Uses fixed-point theorem to show no computable function can take index of decidable c.e. set and return index of its characteristic function; also mentions quines.

---


### cmp/thy/slf — Defining Functions using Self-Reference
- **File**: content/computability/computability-theory/def-functions-self-reference.tex
- **Domain**: CMP
- **Introduces**: (none)
- **References**: THM-CMP005 Recursion Theorem
- **OL Formal Items**: (none - applications)
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: cmp/thy/fix
- **OL Cross-refs**: (none)
- **Notes**: Shows how fixed-point theorem justifies self-referential definitions; example: $\fn{gcd}$ defined recursively.

---

# SUMMARY STATISTICS

## Taxonomy Coverage
- **PRIMs introduced**: PRIM-CMP001, PRIM-CMP002, PRIM-CMP003, PRIM-CMP006, PRIM-CMP007, PRIM-CMP008, PRIM-CMP009, PRIM-CMP010, PRIM-CMP011, PRIM-CMP012 (10/12 PRIMs)
- **DEFs introduced**: DEF-CMP001, DEF-CMP002, DEF-CMP003, DEF-CMP005, DEF-CMP008, DEF-CMP010 (6/10 DEFs)
- **THMs introduced**: THM-CMP002, THM-CMP003, THM-CMP004, THM-CMP005 (4/5 THMs)
- **Missing from registry**: PRIM-CMP004 Turing Machine, PRIM-CMP005 Church-Turing Thesis (mentioned but not OL focus), DEF-CMP004 Enumeration (mentioned), DEF-CMP006 Lambda-Definable, DEF-CMP007 Productive Set, DEF-CMP009 Representability, THM-CMP001 Equivalence of Models

## Role Distribution
- **DEFINE**: 12 sections (core definitions)
- **PROVE**: 13 sections (theorems)
- **APPLY**: 7 sections (examples/applications)
- **DISCUSS**: 5 sections (motivation/context)

## Compression Signals
- **CORE-DEF**: 9 sections
- **CORE-THM**: 13 sections
- **STEPPING-STONE**: 3 sections
- **PEDAGOGICAL**: 16 sections
- **TANGENTIAL**: 1 section

## Key Observations
1. **Heavy pedagogical scaffolding**: ~40% of sections are pedagogical rather than essential to the logical development
2. **Duplicate coverage**: Normal Form Theorem and Halting Problem appear in both chapters with slight variations
3. **Implicit taxonomy elements**: Church-Turing thesis, Turing machines themselves are referenced but not formally developed in these chapters
4. **Strong dependency chain**: Most sections have clear pedagogical prerequisites within their chapter
5. **Cross-chapter dependencies**: Computability-theory chapter depends heavily on recursive-functions chapter
### Chapter: machines-computations

### tur/mac/int — Introduction
- **File**: content/turing-machines/machines-computations/introduction.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP004 Turing Machine (conceptual intro), PRIM-CMP001 Computable Function (conceptual)
- **References**: PRIM-BST012 Natural Number
- **OL Formal Items**:
  - explain (lines 29-84) → OL-ONLY: pedagogical explanation of TM mechanism
  - digress (lines 86-108) → OL-ONLY: philosophical discussion
  - history (lines 110-128) → OL-ONLY: historical context
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none - chapter introduction)
- **OL Cross-refs**: fig:tm
- **Notes**: Purely expository section introducing intuitive concepts of TMs, effective procedures, and Church-Turing thesis context. No formal definitions.

---


### tur/mac/tur — Turing Machines
- **File**: content/turing-machines/machines-computations/turing-machines.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP004 Turing Machine (formal definition)
- **References**: PRIM-BST010 Finite Sequence, PRIM-BST009 Function (partial)
- **OL Formal Items**:
  - defn (lines 22-35): Turing machine → PRIM-CMP004
  - ex (lines 50-60): Even machine → OL-ONLY: example
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: tur/mac/int
- **OL Cross-refs**: (none)
- **Notes**: Core formal definition of Turing machine as 4-tuple. Essential primitive definition.

---


### tur/mac/hal — Halting States
- **File**: content/turing-machines/machines-computations/halting-states.tex
- **Domain**: CMP
- **Introduces**: (none - discusses variation)
- **References**: PRIM-CMP004 Turing Machine
- **OL Formal Items**:
  - ex (lines 25-66) → OL-ONLY: halting state examples
  - explain (lines 68-77) → OL-ONLY: discussion
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: (none)
- **Notes**: Discusses alternative TM formulation with dedicated halting states. Not essential for core theory.

---


### cmp/tur/con — Configurations and Computations
- **File**: content/turing-machines/machines-computations/configuration.tex
- **Domain**: CMP
- **Introduces**: DEF-CMP001 Partial Function (implicit), OL-ONLY: Configuration concept, OL-ONLY: Run/Computation
- **References**: PRIM-CMP004 Turing Machine, PRIM-BST010 Finite Sequence, PRIM-BST012 Natural Number
- **OL Formal Items**:
  - defn (lines 25-38): Configuration → OL-ONLY: foundational concept
  - defn (lines 51-56): Initial configuration → OL-ONLY: foundational concept
  - defn (lines 63-82): One-step yields relation → OL-ONLY: foundational concept
  - defn (lines 84-95): Run, halting, output → OL-ONLY: foundational concepts
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: \olref[rep]{ex:doubler}
- **Notes**: Formalizes TM execution semantics. Critical for connecting TMs to functions they compute. Note olfileid uses "cmp/tur/con" not "tur/mac/con".

---


### tur/mac/una — Unary Representation of Numbers
- **File**: content/turing-machines/machines-computations/unary-numbers.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP001 Computable Function (formal: TM computes function)
- **References**: PRIM-CMP004 Turing Machine, PRIM-BST012 Natural Number, DEF-CMP001 Partial Function
- **OL Formal Items**:
  - defn (lines 24-31): TM computes function → PRIM-CMP001
  - ex (lines 38-64): Adder machine → OL-ONLY: example
  - ex (lines 82-129): Doubler (disciplined version) → OL-ONLY: example
  - ex (lines 131-185): Mover machine → OL-ONLY: example
  - defn (lines 226-235): TM computes partial function → DEF-CMP001
  - prob (lines 33-36, 66-70, 187-196, 198-203, 204-214, 216-224) → OL-ONLY: exercises
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: cmp/tur/con
- **OL Cross-refs**: \olref[rep]{ex:doubler}, \olref[una]{ex:adder}, \olref[una]{ex:mover}, \olref[una]{fig:doubler-disc}
- **Notes**: Defines what it means for a TM to compute a function using unary notation. Essential connection between machines and functions.

---


### tur/mac/var — Variants of Turing Machines
- **File**: content/turing-machines/machines-computations/variants.tex
- **Domain**: CMP
- **Introduces**: THM-CMP001 Equivalence of Computation Models (discussed informally)
- **References**: PRIM-CMP004 Turing Machine
- **OL Formal Items**:
  - (no formal environments, pure exposition)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: \olref[hal]{sec}, \olref[una]{ex:mover}
- **Notes**: Discusses various TM formulations and argues they're all equivalent in computational power. Informal treatment of robustness.

---


### tur/mac/ctt — The Church-Turing Thesis
- **File**: content/turing-machines/machines-computations/church-turing-thesis.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP005 Church-Turing Thesis
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP004 Turing Machine
- **OL Formal Items**:
  - defn (lines 23-26): Church-Turing Thesis → PRIM-CMP005
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: (none)
- **Notes**: Defines the Church-Turing thesis as claim that effective computability = Turing computability. Central philosophical/methodological principle.

---


### tur/mac/rep — Representing Turing Machines
- **File**: content/turing-machines/machines-computations/representing-tms.tex
- **Domain**: CMP
- **Introduces**: (none - introduces representation methods)
- **References**: PRIM-CMP004 Turing Machine
- **OL Formal Items**:
  - ex (lines 39-64): Even machine (state diagram) → OL-ONLY: representation method
  - explain (lines 66-149) → OL-ONLY: pedagogical explanation of configurations
  - ex (lines 150-199): Machine tables → OL-ONLY: representation method
  - ex (lines 209-255): Doubler machine → OL-ONLY: example
  - prob (lines 257-260, 262-271, 272-277, 279-286, 288-295) → OL-ONLY: exercises
- **Role**: APPLY
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: \olref{fig:tm}, \olref{ex:doubler}, \olref{fig:doubler}
- **Notes**: Presents state diagrams and machine tables as ways to represent TMs. Entirely pedagogical.

---


### tur/mac/dis — Disciplined Machines
- **File**: content/turing-machines/machines-computations/disciplined-machines.tex
- **Domain**: CMP
- **Introduces**: OL-ONLY: disciplined TM (technical convenience)
- **References**: PRIM-CMP004 Turing Machine, PRIM-CMP001 Computable Function
- **OL Formal Items**:
  - defn (lines 27-35): Disciplined TM → OL-ONLY: technical definition
  - ex (lines 52-77): Disciplined adder → OL-ONLY: example
  - prop (lines 79-84): Disciplined TMs compute same functions → OL-ONLY: lemma
  - prob (lines 86-88, 91-94) → OL-ONLY: exercises
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: tur/mac/una, \olref[hal]{sec}
- **OL Cross-refs**: \olref[una]{ex:adder}, \olref{fig:adder-disc}, \olref{defn:disciplined}
- **Notes**: Introduces technical restriction to simplify machine composition proofs. Useful but not fundamental.

---


### tur/mac/cmb — Combining Turing Machines
- **File**: content/turing-machines/machines-computations/combining-machines.tex
- **Domain**: CMP
- **Introduces**: OL-ONLY: machine composition operation
- **References**: PRIM-CMP004 Turing Machine, PRIM-CMP001 Computable Function, PRIM-BST009 Function (composition)
- **OL Formal Items**:
  - explain (lines 12-56) → formal construction of $M \frown M'$
  - ex (lines 58-150): Combined adder+doubler → OL-ONLY: example
  - prop (lines 152-156): Composition preserves computability → OL-ONLY: lemma
  - proof (lines 158-164) → OL-ONLY: proof
  - prob (lines 166-170) → OL-ONLY: exercise
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: tur/mac/dis
- **OL Cross-refs**: \olref[mac][dis]{sec}, \olref[mac][cmb]{sec}, \olref{fig:combined}, \olref[dis]{defn:disciplined}, \cref{tur:mac:dis:prob:disc-succ}, \cref{tur:mac:dis:prob:copier}
- **Notes**: Shows how to compose TMs sequentially. Important for proving closure properties and building complex machines.

---

## Chapter: Undecidability


### tur/und/enu — Enumerating Turing Machines
- **File**: content/turing-machines/undecidability/enumerating-tms.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP011 Godel Numbering (for TMs), DEF-CMP005 Index (Program)
- **References**: PRIM-CMP004 Turing Machine, PRIM-BST016 Cardinality, PRIM-BST010 Finite Sequence, PRIM-BST012 Natural Number
- **OL Formal Items**:
  - explain (lines 12-117) → encoding scheme for TMs
  - thm (lines 119-143): Uncomputable functions exist → OL-ONLY: consequence of enumeration
  - prob (lines 145-151) → OL-ONLY: exercise
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: tur/mac/tur
- **OL Cross-refs**: \olref{fig:variants}, \olref{fig:standard-even}, \cref{sfr:siz:zigzag:prob:posint-star}, \cref{sfr:siz:red:prob:nat-nat}
- **Notes**: Shows TMs can be enumerated, introduces indexing. Essential for talking about TMs computing functions of TM codes.

---


### Chapter: undecidability

### tur/und/int — Introduction
- **File**: content/turing-machines/undecidability/introduction.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP006 Decidable Set (conceptual), PRIM-CMP008 Halting Problem (conceptual)
- **References**: PRIM-CMP001 Computable Function, PRIM-CMP004 Turing Machine, PRIM-BST012 Natural Number, PRIM-BST016 Cardinality
- **OL Formal Items**:
  - (no formal environments, expository)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: tur/mac chapters
- **OL Cross-refs**: (none)
- **Notes**: Motivates undecidability, discusses cardinality argument, previews halting problem and decision problem.

---


### tur/und/hal — The Halting Problem
- **File**: content/turing-machines/undecidability/halting-problem.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP008 Halting Problem, THM-CMP002 Unsolvability of Halting Problem
- **References**: PRIM-CMP004 Turing Machine, DEF-CMP005 Index (Program), PRIM-CMP010 Diagonalization (used in proof)
- **OL Formal Items**:
  - defn (lines 25-34): Halting function → PRIM-CMP008
  - defn (lines 36-39): Halting Problem → PRIM-CMP008
  - defn (lines 50-58): Function s → OL-ONLY: auxiliary definition
  - lem (lines 60-96): s is not Turing computable → OL-ONLY: lemma (uses diagonalization)
  - thm (lines 98-113): Unsolvability of Halting Problem → THM-CMP002
  - prob (lines 115-120, 122-126, 128-136, 138-147) → OL-ONLY: exercises
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: tur/mac chapters
- **OL Cross-refs**: \olref[mac][dis]{sec}, \olref[mac][cmb]{sec}, \cref{tur:mac:dis:prob:copier}, \olref[tur][und][enu]{sec}
- **Notes**: Central undecidability result using diagonalization. Foundational theorem in computability theory.

---


### tur/und/rep — Representing Turing Machines
- **File**: content/turing-machines/undecidability/representing-tms.tex
- **Domain**: CMP
- **Introduces**: DEF-CMP009 Representability (of TM behavior in FOL)
- **References**: PRIM-CMP004 Turing Machine, PRIM-SYN012 Formula, PRIM-SYN013 Sentence, PRIM-BST012 Natural Number
- **OL Formal Items**:
  - defn (lines 58-74): Language $\Lang L_M$ → OL-ONLY: FOL language for TMs
  - (lines 76-179): Sentences $!T(M,w)$ and $!E(M,w)$ → DEF-CMP009
  - prop (lines 197-204): $!T(M,w) \Entails \num{m} < \num{k}$ → OL-ONLY: lemma
  - prob (lines 206-209) → OL-ONLY: exercise
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: tur/und/enu, FOL chapters
- **OL Cross-refs**: \olref[rep]{defn:tm-descr}, \olref[rep]{rep-right}, \olref[rep]{rep-left}, \olref[rep]{rep-stay}, \olref[rep]{prop:mlessk}
- **Notes**: Encodes TM execution in first-order logic. Technical machinery for decision problem unsolvability.

---


### tur/und/dec — The Decision Problem
- **File**: content/turing-machines/undecidability/decision-problem.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP006 Decidable Set (applied to FOL validity)
- **References**: PRIM-CMP008 Halting Problem, PRIM-SYN012 Formula, PRIM-SYN013 Sentence, DEF-CMP009 Representability
- **OL Formal Items**:
  - (no formal environments, expository)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: tur/und/hal
- **OL Cross-refs**: (none)
- **Notes**: Sets up strategy for proving decision problem unsolvable by reduction from halting problem.

---


### tur/und/ver — Verifying the Representation
- **File**: content/turing-machines/undecidability/verification.tex
- **Domain**: CMP
- **Introduces**: (none - proves correctness)
- **References**: DEF-CMP009 Representability, PRIM-CMP004 Turing Machine, PRIM-SYN013 Sentence
- **OL Formal Items**:
  - defn (lines 60-72): $!C(M,w,n)$ → OL-ONLY: configuration sentence
  - lem (lines 74-99): Halt config implies !E(M,w) → OL-ONLY: lemma
  - lem (lines 107-239): $!T(M,w) \Entails !C(M,w,n)$ → OL-ONLY: lemma
  - lem (lines 261-278): Valid if halt → OL-ONLY: lemma
  - lem (lines 287-320): Halt if valid → OL-ONLY: lemma
  - prob (lines 241-244, 246-250, 252-258) → OL-ONLY: exercises
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: tur/und/rep
- **OL Cross-refs**: \olref{lem:halt-config-implies-halt}, \olref{lem:config}, \olref[rep]{defn:tm-descr}, \olref[rep]{rep-right}, \olref[rep]{rep-left}, \olref[rep]{rep-stay}, \olref[rep]{prop:mlessk}, \olref{lem:valid-if-halt}, \olref{lem:halt-if-valid}
- **Notes**: Technical proof that FOL representation is correct. Long and detailed but essential for decision problem result.

---


### tur/und/uni — Universal Turing Machines
- **File**: content/turing-machines/undecidability/universal-tm.tex
- **Domain**: CMP
- **Introduces**: PRIM-CMP012 Universal Turing Machine
- **References**: PRIM-CMP004 Turing Machine, DEF-CMP005 Index, PRIM-CMP011 Godel Numbering
- **OL Formal Items**:
  - defn (lines 24-28): Index → DEF-CMP005
  - thm (lines 59-137): Universal Turing machine exists → PRIM-CMP012
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: tur/und/enu
- **OL Cross-refs**: \olref[enu]{sec}
- **Notes**: Proves existence of universal TM that simulates any TM. Major theorem showing TMs can interpret TM codes.

---


### tur/und/uns — The Decision Problem is Unsolvable
- **File**: content/turing-machines/undecidability/unsolvability-decision-problem.tex
- **Domain**: CMP
- **Introduces**: THM-CMP002 (extension: decision problem unsolvable)
- **References**: PRIM-CMP008 Halting Problem, PRIM-CMP004 Turing Machine, DEF-CMP009 Representability, PRIM-CMP006 Decidable Set, PRIM-CMP007 Semi-Decidable (c.e.) Set
- **OL Formal Items**:
  - thm (lines 12-37): Decision problem unsolvable → THM-CMP002 extension
  - cor (lines 39-58): Satisfiability undecidable → OL-ONLY: corollary
  - thm (lines 70-89): Validity is semi-decidable → PRIM-CMP007 (example)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: tur/und/ver
- **OL Cross-refs**: \olref[ver]{lem:halt-if-valid}, \olref[ver]{lem:valid-if-halt}, \olref[hal]{thm:halting-problem}, \cref{tur:und:uns:thm:decision-prob}, \cref{tur:und:uns:cor:undecidable-sat}, \olref{thm:valid-ce}
- **Notes**: Main result: FOL validity/satisfiability is undecidable. Also shows validity is semi-decidable. Major theorem connecting logic and computability.

---


### tur/und/tra — Trakhtenbrot's Theorem
- **File**: content/turing-machines/undecidability/trakhtenbrot.tex
- **Domain**: CMP
- **Introduces**: OL-ONLY: Trakhtenbrot's Theorem (finite satisfiability undecidable)
- **References**: PRIM-CMP008 Halting Problem, DEF-CMP009 Representability, PRIM-CMP006 Decidable Set
- **OL Formal Items**:
  - (lines 89-161): Modified $!T'(M,w)$ → OL-ONLY: technical variant
  - lem (lines 165-185): Halt implies finite model → OL-ONLY: lemma
  - lem (lines 192-215): Finite model implies halt → OL-ONLY: lemma
  - thm (lines 223-237): Trakhtenbrot's Theorem → OL-ONLY: advanced result
  - cor (lines 239-247): No sound/complete proof system for finite validity → OL-ONLY: corollary
  - prob (lines 68-86, 187-190, 217-221, 249-257) → OL-ONLY: exercises
- **Role**: PROVE
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: tur/und/uns
- **OL Cross-refs**: \olref[rep]{sec}, \olref[ver]{lem:valid-if-halt}, \olref[ver]{lem:halt-if-valid}, \olref[ver]{lem:config}, \olref[rep]{prop:mlessk}, \cref{tur:und:uns:thm:decision-prob}, \cref{tur:und:uns:cor:undecidable-sat}, \olref[uns]{thm:valid-ce}, \olref{lem:halts-sat}, \olref{lem:sat-halts}, \olref{cor:fproof-incomp}
- **Notes**: Advanced result showing finite satisfiability also undecidable. Extension beyond core material, uses refined encoding.

---

## Summary Statistics

**Total files processed**: 21 files (11 machines-computations + 10 undecidability)

**Taxonomy coverage**:
- **PRIMs introduced**: PRIM-CMP001 (Computable Function), PRIM-CMP004 (Turing Machine), PRIM-CMP005 (Church-Turing Thesis), PRIM-CMP006 (Decidable Set), PRIM-CMP008 (Halting Problem), PRIM-CMP010 (Diagonalization, used), PRIM-CMP011 (Godel Numbering), PRIM-CMP012 (Universal Turing Machine)
- **DEFs introduced**: DEF-CMP001 (Partial Function), DEF-CMP005 (Index), DEF-CMP009 (Representability)
- **THMs introduced**: THM-CMP001 (Equivalence of Computation Models, informal), THM-CMP002 (Unsolvability of Halting Problem + Decision Problem)
- **Other taxonomy referenced**: PRIM-BST009, PRIM-BST010, PRIM-BST012, PRIM-BST016, PRIM-SYN012, PRIM-SYN013

**Compression signals**:
- CORE-DEF: 6 files (tur, con, una, ctt, enu, rep)
- CORE-THM: 3 files (hal, uni, uns)
- STEPPING-STONE: 4 files (dis, cmb, dec, ver)
- PEDAGOGICAL: 5 files (int, hal-states, var, rep-representing, und/int)
- TANGENTIAL: 1 file (tra)
- DISCUSS: 2 files (int, und/int)

**OL-specific content**: Many examples, exercises (prob), state diagrams, historical/philosophical discussions not in core CMP taxonomy.


## Batch 4 — METATHEORY (completeness + models-theories + beyond)


## Chapter: completeness

### fol/com/int — Introduction
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/introduction.tex`
- **Domain**: METATHEORY
- **Introduces**: (none -- motivational overview)
- **References**: PRIM-SEM010 (logical consequence), PRIM-DED001 (derivability), CP-002 (completeness, previewed informally), CP-003 (compactness, previewed informally), CP-004 (Lowenheim-Skolem, previewed informally), DEF-SEM004 (semantic consistency, informally)
- **OL Formal Items**: (none -- no formal environments)
- **Role**: DISCUSS
- **Variant Tags**: `\iftag{FOL}` used throughout for structure vs. valuation language
- **Dual ID**: FOL=fol/com/int, PL=pl/com/int
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none -- first section of chapter)
- **OL Cross-refs**: (none)
- **Notes**: Previews all major results of the chapter (completeness, compactness, Lowenheim-Skolem) without formal statements. Mentions Hilbert's letter to Frege as historical motivation. No formal items to map.

---

### fol/com/out — Outline of the Proof
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/outline.tex`
- **Domain**: METATHEORY
- **Introduces**: (none -- pedagogical road map)
- **References**: CP-002 (completeness theorem, outlined), DEF-DED002 (maximally consistent set, implicitly), DEF-SEM003 (consistency-as-satisfiability link), PRIM-DED001 (derivability), PRIM-SEM010 (entailment)
- **OL Formal Items**: (none -- no thm/defn/lem/prop environments)
- **Role**: DISCUSS
- **Variant Tags**: `\iftag{FOL}` used throughout for structure vs. valuation language
- **Dual ID**: FOL=fol/com/out, PL=pl/com/out
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/com/int
- **OL Cross-refs**: `\olref[ccs]{prop:ccs}`, `\olref[hen]{defn:henkin-exp}`, `\olref[hen]{lem:henkin}`, `\olref[hen]{prop:saturated-instances}`, `\olref[lin]{lem:lindenbaum}`, `\olref[mod]{defn:termmodel}`, `\olref[mod]{lem:truth}`, `\olref[ide]{defn:term-model-factor}`, `\olref[ide]{lem:truth}`
- **Notes**: Provides a prose overview of the entire Henkin construction proof strategy. References nearly every subsequent section. Purely pedagogical -- no new formal content. Highly useful as a reading guide but fully compressible.

---

### fol/com/ccs — Complete Consistent Sets of Sentences
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/complete-consistent-sets.tex`
- **Domain**: DED (deductive properties of sentence sets)
- **Introduces**: DEF-SEM005 (Complete Theory / Complete set of sentences -- `def:complete-set`)
- **References**: PRIM-DED001 (derivability / $\Proves$), DEF-DED001 (consistency), DEF-DED005 (provability properties -- reflexivity, monotonicity, transitivity)
- **OL Formal Items**:
  - defn[def:complete-set] -> DEF-SEM005 (Complete set / Complete theory)
  - prop[prop:ccs] -> OL-ONLY: stepping stone for CP-002 (properties of complete consistent sets: closure under provability, connective conditions)
  - prop[prop:ccs-prov-in] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:ccs-and] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:ccs-or] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:ccs-if] -> OL-ONLY: stepping stone for CP-002
- **Role**: DEFINE / PROVE
- **Variant Tags**: `\iftag{FOL}` for dual, `\tagitem{prvAnd}`, `\tagitem{prvOr}`, `\tagitem{prvIf}`, `\tagitem{defAnd}`, `\tagitem{defOr}`, `\tagitem{defIf}`, `\iftag{probAnd}`, `\iftag{probOr}`, `\iftag{probIf}`
- **Dual ID**: FOL=fol/com/ccs, PL=pl/com/ccs
- **Compression Signal**: CORE-DEF (for DEF-SEM005), STEPPING-STONE (for prop:ccs)
- **Ped. Prerequisites**: fol/com/out
- **OL Cross-refs**: `\tagrefs{prfSC/{fol:seq:ptn:sec}, prfND/{fol:ntd:ptn:sec}, ...}` (properties of $\Proves$), `\tagrefs{prfSC/{fol:seq:prv:prop:explicit-inc},...}`, `\tagrefs{prfSC/{fol:seq:ppr:prop:provability-land},...}`, `\tagrefs{prfSC/{fol:seq:ppr:prop:provability-lor},...}`, `\tagrefs{prfSC/{fol:seq:ppr:prop:provability-lif},...}`
- **Notes**: The definition of "complete set" here is the same concept as DEF-SEM005 (Complete Theory) but phrased in terms of sentence membership rather than entailment closure. prop:ccs is the key technical lemma used in the Truth Lemma. MCS section (below) gives the alternative characterization. The OL uses "complete" as a token, so it can be swapped between "complete" and "maximally consistent" via tagging.

---

### fol/com/mcs — Maximally Consistent Sets of Sentences
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/maximally-consistent-sets.tex`
- **Domain**: DED
- **Introduces**: DEF-DED002 (Maximally Consistent Set -- `mcs`)
- **References**: DEF-DED001 (consistency), PRIM-DED001 (derivability), DEF-SEM005 (completeness, since every MCS is complete)
- **OL Formal Items**:
  - defn[mcs] -> DEF-DED002 (Maximally consistent set)
  - prop[prop:mcs] -> OL-ONLY: stepping stone for CP-002 (properties of MCS: closure under provability, either-or, connective conditions)
  - prop[prop:mcs-prov-in] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:mcs-either-or] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:mcs-and] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:mcs-or] -> OL-ONLY: stepping stone for CP-002
  - prop[prop:mcs-if] -> OL-ONLY: stepping stone for CP-002
- **Role**: DEFINE / PROVE
- **Variant Tags**: `\tagitem{prvAnd}`, `\tagitem{prvOr}`, `\tagitem{prvIf}`, `\tagitem{defAnd}`, `\tagitem{defOr}`, `\tagitem{defIf}`, `\iftag{probAnd}`, `\iftag{probOr}`, `\iftag{probIf}`
- **Dual ID**: FOL=fol/com/mcs (only -- no PL dual in iftag; file has only `\olfileid{fol}{com}{mcs}`)
- **Compression Signal**: CORE-DEF (for DEF-DED002), STEPPING-STONE (for prop:mcs)
- **Ped. Prerequisites**: fol/com/ccs
- **OL Cross-refs**: `\tagrefs{prfSC/{fol:seq:prv:prop:provability-contr},...}`, `\tagrefs{prfSC/{fol:seq:prv:prop:provability-exhaustive},...}`, `\tagrefs{prfSC/{fol:seq:prv:prop:provability-land-left},...}`, etc.
- **Notes**: The file header comment says "Properties of mcs required for completeness proved are in maximally-consistent-sets.tex in the chapter on the proof system used," indicating there are companion files in the proof-system chapters. The prop:mcs results mirror those of prop:ccs; the OL provides both because the "complete consistent set" vs "maximally consistent set" approaches are tagged alternatives. Only the FOL olfileid is present (no PL variant).

---

### fol/com/hen — Henkin Expansion
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/henkin-expansions.tex`
- **Domain**: DED / METATHEORY
- **Introduces**: OL-ONLY: Saturated set (defn, unnamed taxonomy -- stepping stone for CP-002), OL-ONLY: Henkin expansion construction (defn:henkin-exp)
- **References**: DEF-DED001 (consistency), PRIM-SYN003 (language/constant symbols), DEF-SEM005 (complete set), PRIM-DED001 (derivability), DEF-DED005 (provability properties)
- **OL Formal Items**:
  - prop[prop:lang-exp] -> OL-ONLY: stepping stone for CP-002 (language expansion preserves consistency)
  - defn (Saturated set, unlabeled) -> OL-ONLY: stepping stone for CP-002
  - defn[defn:henkin-exp] -> OL-ONLY: stepping stone for CP-002 (Henkin witness sentences $D_n$)
  - lem[lem:henkin] -> OL-ONLY: stepping stone for CP-002 (every consistent set extends to saturated consistent set)
  - prop[prop:saturated-instances] -> OL-ONLY: stepping stone for CP-002 (quantifier instances in saturated complete consistent sets)
- **Role**: DEFINE / PROVE
- **Variant Tags**: `\iftag{prvEx}`, `\iftag{prvAll}`, `\iftag{defAll,defEx}`, `\iftag{probEx}`, `\iftag{probAll}`
- **Dual ID**: FOL=fol/com/hen (only -- no PL dual; FOL-only section)
- **Compression Signal**: STEPPING-STONE (all items serve CP-002)
- **Ped. Prerequisites**: fol/com/ccs
- **OL Cross-refs**: `\olref[ccs]{prop:ccs}`, `\olref[ccs]{prop:ccs-prov-in}`, `\tagrefs{prfAX/{fol:axd:qpr:thm:strong-generalization},...}`, `\tagrefs{prfAX/{fol:axd:ppr:prop:provability-lif},...}`, `\tagrefs{prfAX/{fol:axd:qpr:prop:provability-quantifiers},...}`
- **Notes**: This is the core of the Henkin trick. FOL-only (no propositional logic variant since PL has no quantifiers). The saturated set definition and Henkin expansion are specific to the completeness proof and do not appear in the taxonomy as standalone primitives. The `\iftag{prvEx}` vs `\iftag{prvAll}` branching handles whether the proof system treats existentials or universals as primitive.

---

### fol/com/lin — Lindenbaum's Lemma
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/lindenbaums-lemma.tex`
- **Domain**: DED
- **Introduces**: THM-DED005 (Lindenbaum's Lemma -- `lem:lindenbaum`)
- **References**: DEF-DED001 (consistency), DEF-SEM005 (complete set), DEF-DED005 (provability properties / proves-compact)
- **OL Formal Items**:
  - lem[lem:lindenbaum] -> THM-DED005 (Lindenbaum's Lemma: every consistent set extends to a complete consistent set)
- **Role**: PROVE
- **Variant Tags**: `\iftag{FOL}` for dual
- **Dual ID**: FOL=fol/com/lin, PL=pl/com/lin
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/com/ccs (or fol/com/mcs depending on tag)
- **OL Cross-refs**: `\tagrefs{prfAX/{fol:axd:prv:prop:provability-exhaustive},...}`, `\tagrefs{prfAX/{fol:axd:ptn:prop:proves-compact},...}`
- **Notes**: Key lemma in the completeness proof. The proof uses a standard enumeration-and-extension argument. Uses the compactness of $\Proves$ (if every finite subset of $\Gamma^*$ is consistent, then $\Gamma^*$ is consistent). This is a core DED result independent of the completeness theorem, widely reused.

---

### fol/com/mod — Construction of a Model
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/construction-of-model.tex`
- **Domain**: SEM / METATHEORY
- **Introduces**: OL-ONLY: Term model (defn:termmodel -- stepping stone for CP-002), OL-ONLY: Truth Lemma (lem:truth -- stepping stone for CP-002)
- **References**: DEF-SEM005 (complete set), DEF-DED001 (consistency), PRIM-SEM001-004 (structure, domain, interpretation), PRIM-SEM006 (satisfaction), PRIM-SYN003 (terms, constants, functions, predicates)
- **OL Formal Items**:
  - defn[defn:termmodel] -> OL-ONLY: stepping stone for CP-002 (term model $\mathfrak{M}(\Gamma^*)$ / valuation $v(\Gamma^*)$)
  - lem[lem:val-in-termmodel] -> OL-ONLY: stepping stone for CP-002 (value of term in term model)
  - prop[prop:quant-termmodel] -> OL-ONLY: stepping stone for CP-002 (quantifiers in term model reduce to instances)
  - lem[lem:truth] -> OL-ONLY: stepping stone for CP-002 (Truth Lemma: $\mathfrak{M}(\Gamma^*) \models A$ iff $A \in \Gamma^*$)
- **Role**: DEFINE / PROVE
- **Variant Tags**: `\iftag{FOL}` throughout (FOL gets term model, PL gets valuation), `\tagitem{prvFalse}`, `\tagitem{prvTrue}`, `\tagitem{FOL}` (for atomic case), `\tagitem{prvNot}`, `\tagitem{prvAnd}`, `\tagitem{prvOr}`, `\tagitem{prvIf}`, `\tagitem{prvAll}`, `\tagitem{prvEx}`, plus `\iftag{probAnd}`, `\iftag{probOr}`, `\iftag{probIf}`, `\iftag{probEx}`, `\iftag{probAll}`
- **Dual ID**: FOL=fol/com/mod, PL=pl/com/mod
- **Compression Signal**: STEPPING-STONE (critical stepping stone -- the heart of the Henkin construction)
- **Ped. Prerequisites**: fol/com/ccs (or fol/com/mcs), fol/com/hen (FOL only), fol/com/lin
- **OL Cross-refs**: `\olref[ccs]{prop:ccs}`, `\olref[ccs]{prop:ccs-and}`, `\olref[ccs]{prop:ccs-or}`, `\olref[ccs]{prop:ccs-if}`, `\olref[ccs]{prop:ccs-prov-in}`, `\olref[hen]{prop:saturated-instances}`, `\olref[syn][ass]{prop:sat-quant}`, `\olref[fol][syn][ext]{prop:ext-formulas}`, `\olref[fol][syn][ass]{prop:sentence-sat-true}`
- **Notes**: This is the central construction of the completeness proof. The term model definition and Truth Lemma together constitute the main technical content. The Truth Lemma is proved by induction on formula complexity. In the PL case, the construction reduces to a simple valuation derived from $\Gamma^*$. The term model and Truth Lemma are not standalone taxonomy items -- they exist specifically to serve CP-002.

---

### fol/com/ide — Identity
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/identity.tex`
- **Domain**: SEM / METATHEORY
- **Introduces**: OL-ONLY: Factored term model / equivalence classes (defn:term-model-factor -- stepping stone for CP-002)
- **References**: DEF-SEM005 (complete set), DEF-DED001 (consistency), PRIM-SEM001 (structure), PRIM-SYN007 (identity symbol $=$), PRIM-SEM006 (satisfaction)
- **OL Formal Items**:
  - defn (unlabeled: $\approx$ relation on closed terms) -> OL-ONLY: stepping stone for CP-002
  - prop[prop:approx-equiv] -> OL-ONLY: stepping stone for CP-002 ($\approx$ is a congruence)
  - defn (unlabeled: equivalence class $[t]_\approx$) -> OL-ONLY: stepping stone for CP-002
  - defn[defn:term-model-factor] -> OL-ONLY: stepping stone for CP-002 (factored term model $\mathfrak{M}/{\approx}$)
  - lem[lem:val-in-termmodel-factored] -> OL-ONLY: stepping stone for CP-002
  - lem[lem:truth] -> OL-ONLY: stepping stone for CP-002 (Truth Lemma for factored model)
- **Role**: DEFINE / PROVE
- **Variant Tags**: (none -- FOL-only section, no iftag)
- **Dual ID**: FOL=fol/com/ide (only -- no PL dual; identity is FOL-only)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/com/mod
- **OL Cross-refs**: `\olref[mod]{defn:termmodel}`, `\olref[mod]{lem:val-in-termmodel}`, `\olref[mod]{lem:truth}`
- **Notes**: Extends the term model construction to handle identity. The factoring construction (quotienting by $\approx$) is a standard algebraic technique. The digress block notes that $\mathfrak{M}/{\approx}$ may be finite even though $\mathfrak{M}(\Gamma^*)$ is always countably infinite. This section is FOL-only since PL has no identity.

---

### fol/com/cth — The Completeness Theorem
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/completeness-thm.tex`
- **Domain**: METATHEORY
- **Introduces**: CP-002 (Completeness Theorem -- `thm:completeness` and `cor:completeness`)
- **References**: THM-DED005 (Lindenbaum's Lemma), PRIM-DED001 (derivability), PRIM-SEM010 (entailment), DEF-DED001 (consistency), DEF-SEM003 (satisfiability), CP-001 (soundness, via tagrefs to prov-incons)
- **OL Formal Items**:
  - thm[thm:completeness] -> CP-002 (first formulation: consistent implies satisfiable)
  - cor[cor:completeness] -> CP-002 (second formulation: $\Gamma \models A \Rightarrow \Gamma \vdash A$)
- **Role**: PROVE
- **Variant Tags**: `\iftag{FOL}` for dual
- **Dual ID**: FOL=fol/com/cth, PL=pl/com/cth
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: fol/com/hen, fol/com/lin, fol/com/mod, fol/com/ide (all stepping stones)
- **OL Cross-refs**: `\olref[hen]{lem:henkin}`, `\olref[lin]{lem:lindenbaum}`, `\olref[mod]{lem:truth}`, `\olref[ide]{lem:truth}`, `\olref[syn][sem]{prop:entails-unsat}`, `\tagrefs{prfAX/{fol:axd:prv:prop:prov-incons},...}`
- **Notes**: The culminating result of the chapter. The proof assembles all the stepping stones: Henkin expansion, Lindenbaum's Lemma, and the Truth Lemma. The corollary derives the entailment-to-derivability formulation from the consistency-to-satisfiability formulation via contraposition and the link between unsatisfiability and inconsistency. CP-001 (soundness) is used implicitly in the proof of (2) from (1) via the prov-incons references. The problem asks students to show the two formulations are equivalent.

---

### fol/com/com — The Compactness Theorem
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/compactness.tex`
- **Domain**: METATHEORY
- **Introduces**: CP-003 (Compactness Theorem -- `thm:compactness`), DEF-SEM003 (Finitely satisfiable -- defn in text)
- **References**: CP-002 (completeness, `\olref[cth]{thm:completeness}`), CP-001 (soundness, via `cor:consistency-soundness`), PRIM-SEM010 (entailment), DEF-SEM002 (satisfiability), DEF-DED001 (consistency), DEF-DED005 (proves-compact)
- **OL Formal Items**:
  - defn (unlabeled: finitely satisfiable) -> DEF-SEM003
  - thm[thm:compactness] -> CP-003 (Compactness Theorem, both formulations)
  - ex (covered model) -> OL-ONLY: PEDAGOGICAL (application of compactness)
  - ex (infinitesimals via compactness) -> OL-ONLY: PEDAGOGICAL (application of compactness)
  - ex (finitude not expressible) -> OL-ONLY: PEDAGOGICAL (application of compactness)
- **Role**: PROVE / APPLY
- **Variant Tags**: `\iftag{FOL}` for dual, `\tagprob{FOL}`, `\tagprob{notFOL}`
- **Dual ID**: FOL=fol/com/com, PL=pl/com/com
- **Compression Signal**: CORE-THM (for CP-003 and DEF-SEM003)
- **Ped. Prerequisites**: fol/com/cth
- **OL Cross-refs**: `\olref[cth]{thm:completeness}`, `\tagrefs{prfAX/{fol:axd:sou:cor:consistency-soundness},...}`, `\tagrefs{prfAX/{fol:axd:ptn:prop:proves-compact},...}`
- **Notes**: Proves compactness as a corollary of completeness + soundness. The proof route: finitely satisfiable -> finitely consistent (by soundness) -> consistent (by compactness of $\Proves$) -> satisfiable (by completeness). The examples (covered models, infinitesimals, finitude inexpressibility) are pedagogically valuable applications of compactness. The definition of "finitely satisfiable" is given without a label but is DEF-SEM003.

---

### fol/com/cpd — A Direct Proof of the Compactness Theorem
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/compactness-direct.tex`
- **Domain**: METATHEORY
- **Introduces**: OL-ONLY: Direct compactness proof (thm:compactness-direct -- alternative proof of CP-003)
- **References**: CP-003 (compactness), DEF-SEM003 (finitely satisfiable), DEF-SEM005 (complete set), DEF-DED001 (consistency)
- **OL Formal Items**:
  - prop[prop:fsat-ccs] -> OL-ONLY: stepping stone (properties of complete finitely satisfiable sets)
  - lem[lem:fsat-henkin] -> OL-ONLY: stepping stone (Henkin extension for finitely satisfiable sets, FOL only)
  - prop[prop:fsat-instances] -> OL-ONLY: stepping stone (quantifier instances for finitely satisfiable saturated sets, FOL only)
  - lem[lem:fsat-lindenbaum] -> OL-ONLY: stepping stone (Lindenbaum for finitely satisfiable sets)
  - thm[thm:compactness-direct] -> OL-ONLY: alternative proof of CP-003
- **Role**: PROVE
- **Variant Tags**: `\iftag{FOL}` for dual, `\tagprob{FOL}`, `\tagprob{notFOL}`
- **Dual ID**: FOL=fol/com/cpd, PL=pl/com/cpd
- **Compression Signal**: STEPPING-STONE (alternative proof -- not needed if CP-003 already established via completeness)
- **Ped. Prerequisites**: fol/com/ccs, fol/com/hen, fol/com/lin, fol/com/mod
- **OL Cross-refs**: `\olref[mod]{defn:termmodel}`, `\olref[mod]{prop:quant-termmodel}`, `\olref[mod]{lem:truth}`, `\olref[ccs]{prop:ccs}`, `\olref[hen]{prop:saturated-instances}`, `\olref{prop:fsat-ccs}`, `\olref{prop:fsat-instances}`, `\olref{lem:fsat-henkin}`, `\olref{lem:fsat-lindenbaum}`
- **Notes**: This section provides an alternative proof of compactness that avoids the detour through soundness and completeness. It replaces "consistent" with "finitely satisfiable" throughout the Henkin construction. Pedagogically important as it shows the construction's flexibility, but from a taxonomy perspective it is an alternative proof route for CP-003, not a new result.

---

### fol/com/dls — The Lowenheim-Skolem Theorem
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/completeness/downward-ls.tex`
- **Domain**: METATHEORY
- **Introduces**: CP-004 (Lowenheim-Skolem Theorem, downward -- `thm:downward-ls`)
- **References**: CP-002 (completeness, used in proof), DEF-DED001 (consistency), PRIM-SEM001 (structure/domain), BST-SET004 (denumerability)
- **OL Formal Items**:
  - thm[thm:downward-ls] -> CP-004 (Downward Lowenheim-Skolem: consistent set has countable model)
  - thm[noidentity-ls] -> OL-ONLY: variant of CP-004 (without identity: consistent set has denumerable model)
  - ex (Skolem's Paradox) -> OL-ONLY: PEDAGOGICAL
- **Role**: PROVE / APPLY
- **Variant Tags**: (none -- FOL-only section, no iftag)
- **Dual ID**: FOL=fol/com/dls (only -- no PL dual; FOL-only)
- **Compression Signal**: CORE-THM (for CP-004)
- **Ped. Prerequisites**: fol/com/cth
- **OL Cross-refs**: (implicit reference to completeness proof's term model construction)
- **Notes**: The proof is remarkably short: it follows directly from the fact that the term model constructed in the completeness proof has a domain no larger than the set of terms. The variant without identity gives a stronger result (denumerable, not just countable). Skolem's Paradox example discusses ZFC having countable models despite proving the existence of uncountable sets.

---

## Chapter: models-theories

### fol/mat/int — Introduction
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/introduction.tex`
- **Domain**: SEM
- **Introduces**: DEF-DED003 (Deductive Closure / Closure of a set of sentences -- defn in text), DEF-SEM007 (Axiomatizable Theory -- "axiomatized by" in defn)
- **References**: PRIM-SEM010 (entailment $\Gamma \models A$), PRIM-SEM011 (model of a set $\mathfrak{A} \models \Gamma$), PRIM-SEM001 (structure)
- **OL Formal Items**:
  - defn (unlabeled: Closed set, Closure, Axiomatized by) -> DEF-DED003 (Deductive Closure: $\{A : \Gamma \models A\}$), DEF-SEM007 (Axiomatizable Theory)
- **Role**: DEFINE / DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/int (only -- no dual)
- **Compression Signal**: CORE-DEF (for DEF-DED003 and DEF-SEM007), PEDAGOGICAL (for the expository list)
- **Ped. Prerequisites**: (none -- first section of chapter)
- **OL Cross-refs**: (none)
- **Notes**: The definition uses semantic closure ($\Gamma \models A$) rather than deductive closure ($\Gamma \vdash A$). Strictly speaking, this defines semantic closure; by completeness these coincide, so we map this to DEF-DED003 (deductive closure) as well. The "axiomatized by" notion maps to DEF-SEM007. The explain block provides a rich discussion of the axiomatic method (6 numbered items about capturing structures, consistency, independence, definability). Implicitly introduces PRIM-DED002 (non-logical axiom) in the discussion of axiom systems, though not via a formal definition.

---

### fol/mat/exs — Expressing Properties of Structures
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/expressing-props-of-structures.tex`
- **Domain**: SEM
- **Introduces**: PRIM-SEM011 (Model of a set of sentences -- `defn` labeled "Model of a set")
- **References**: PRIM-SEM001 (structure), PRIM-SEM006 (satisfaction)
- **OL Formal Items**:
  - defn (Model of a set) -> PRIM-SEM011 ($\mathfrak{M}$ is a model of $\Gamma$ iff $\mathfrak{M} \models A$ for all $A \in \Gamma$)
  - ex (partial order axioms) -> OL-ONLY: PEDAGOGICAL
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/exs (only)
- **Compression Signal**: CORE-DEF (for PRIM-SEM011)
- **Ped. Prerequisites**: fol/mat/int
- **OL Cross-refs**: (none)
- **Notes**: This is the defining occurrence of PRIM-SEM011 (model of a set of sentences). The concept was likely used informally earlier, but here it gets a formal definition. The example of partial order axioms illustrates how axiom systems capture classes of structures.

---

### fol/mat/the — Examples of First-Order Theories
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/theories.tex`
- **Domain**: SEM
- **Introduces**: PRIM-DED002 (Non-Logical Axiom / Proper Axiom -- implicit via examples of axiom systems)
- **References**: PRIM-SEM011 (model of a set), DEF-SEM007 (axiomatizable theory), PRIM-SEM001 (structure)
- **OL Formal Items**:
  - ex (strict linear orders) -> OL-ONLY: PEDAGOGICAL (example theory)
  - ex (groups) -> OL-ONLY: PEDAGOGICAL (example theory)
  - ex (Peano arithmetic) -> OL-ONLY: PEDAGOGICAL (example theory, introduces induction schema)
  - ex (pure sets / naive comprehension) -> OL-ONLY: PEDAGOGICAL (example theory, shows inconsistency of naive comprehension)
  - ex (mereology / parthood) -> OL-ONLY: PEDAGOGICAL (example theory)
- **Role**: APPLY / DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/the (only)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/mat/int, fol/mat/exs
- **OL Cross-refs**: (none)
- **Notes**: This section consists entirely of examples. Each example implicitly demonstrates PRIM-DED002 (non-logical axioms) by presenting specific axiom systems. The Peano arithmetic example introduces the induction schema. The naive set theory example demonstrates Russell's Paradox. No formal theorem/definition environments are used -- all items are `\begin{ex}`.

---

### fol/mat/exr — Expressing Relations in a Structure
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/expressing-relations.tex`
- **Domain**: SEM
- **Introduces**: OL-ONLY: "Expresses the relation" (definability in a structure -- defn in text)
- **References**: PRIM-SEM001 (structure), PRIM-SEM006 (satisfaction), PRIM-SYN003 (formula, variable assignment)
- **OL Formal Items**:
  - defn (unlabeled: "$!A$ expresses the relation $R$") -> OL-ONLY: definability concept (not in taxonomy as a separate item, but relates to DEF-SEM008 indirectly)
  - ex (arithmetic relations) -> OL-ONLY: PEDAGOGICAL
- **Role**: DEFINE / DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/exr (only)
- **Compression Signal**: PEDAGOGICAL (the definability concept itself is not a core taxonomy item, though it underpins DEF-SEM008)
- **Ped. Prerequisites**: fol/mat/exs
- **OL Cross-refs**: (none)
- **Notes**: Defines when a formula "expresses" a relation in a particular structure. This is a semantic concept about definability within a fixed structure, distinct from the theory-level concepts. The examples in $\mathfrak{N}$ (standard model of arithmetic) show how to define $\le$, successor, predecessor, and $<$ using arithmetic operations.

---

### fol/mat/set — The Theory of Sets
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/set-theory.tex`
- **Domain**: SEM / SET-THEORETIC FOUNDATIONS
- **Introduces**: (none -- no new taxonomy items; applies previously defined concepts to ZFC)
- **References**: PRIM-DED002 (non-logical axioms, via ZFC axioms), DEF-SEM007 (axiomatizable theory), PRIM-SEM011 (model)
- **OL Formal Items**:
  - (no formal thm/defn/lem environments -- the section is expository with inline formulas)
- **Role**: APPLY / DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/set (only)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/mat/the, fol/mat/exr
- **OL Cross-refs**: (none)
- **Notes**: Extended exposition of how ZFC set theory can be formulated in FOL. Demonstrates how to define $\subseteq$, $\emptyset$, $\cup$, $\mathcal{P}(X)$, ordered pairs, Cartesian products, functions, injectivity, and Cantor's theorem within the language of set theory. Discusses the axiom of extensionality, empty set axiom, power set axiom, comprehension principle vs. separation principle, and Russell's Paradox. Entirely pedagogical from the taxonomy perspective.

---

### fol/mat/siz — Expressing the Size of Structures
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/models-theories/size-of-structures.tex`
- **Domain**: SEM
- **Introduces**: OL-ONLY: $A_{\ge n}$ and $A_{= n}$ sentences (expressing domain cardinality)
- **References**: PRIM-SEM001 (structure/domain), PRIM-SEM006 (satisfaction), PRIM-SYN007 (identity), CP-003 (compactness, referenced in closing), CP-004 (Lowenheim-Skolem, referenced in closing)
- **OL Formal Items**:
  - prop (unlabeled: $A_{\ge n}$ is true iff domain has $\ge n$ elements) -> OL-ONLY: PEDAGOGICAL
  - prop (unlabeled: $A_{= n}$ is true iff domain has exactly $n$ elements) -> OL-ONLY: PEDAGOGICAL
  - prop (unlabeled: structure is infinite iff model of $\{A_{\ge 1}, A_{\ge 2}, \ldots\}$) -> OL-ONLY: PEDAGOGICAL
- **Role**: DISCUSS / APPLY
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/mat/siz (only)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/mat/exs
- **OL Cross-refs**: (implicit references to compactness and Lowenheim-Skolem in final paragraph)
- **Notes**: Shows how FOL can express "at least $n$" and "exactly $n$" elements, and that infinitude is expressible by a set of sentences. States without proof that finitude and non-enumerability cannot be expressed, referencing compactness and Lowenheim-Skolem. This section connects to the completeness chapter's results. The $A_{\ge n}$ sentences are also used in the compactness examples in fol/com/com.

---

## Chapter: beyond

### fol/byd/int — Overview
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/introduction.tex`
- **Domain**: METATHEORY (philosophy of logic)
- **Introduces**: (none)
- **References**: (none from taxonomy)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/int (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: (none -- first section of chapter)
- **OL Cross-refs**: (none)
- **Notes**: Philosophical introduction discussing what makes a system "logical." Mentions Russell-Whitehead Principia, Quine's objections to higher-order logic, Frege's logicist tradition. No formal content whatsoever.

---

### fol/byd/msl — Many-Sorted Logic
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/many-sorted-logic.tex`
- **Domain**: SYNTAX / SEMANTICS (extension)
- **Introduces**: (none from taxonomy -- survey of many-sorted logic)
- **References**: PRIM-SYN003 (variables, quantifiers), PRIM-SEM001 (structure/domain), CP-002 (completeness, mentioned for many-sorted logic)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/msl (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/int
- **OL Cross-refs**: (none)
- **Notes**: Describes many-sorted logic: multiple disjoint domains, typed variables/quantifiers/predicates/functions. Shows how it can be embedded into FOL via sort predicates and relativized quantifiers. Notes completeness theorem carries over. Brief and self-contained.

---

### fol/byd/sol — Second-Order Logic
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/second-order-logic.tex`
- **Domain**: SYNTAX / SEMANTICS / METATHEORY (extension)
- **Introduces**: (none from core taxonomy -- discusses second-order logic as an extension)
- **References**: CP-002 (completeness, for weak semantics), CP-003 (compactness, noted as failing for full SOL), CP-004 (Lowenheim-Skolem, noted as failing for full SOL), DEF-SEM006 (categoricity, discussed for second-order PA)
- **OL Formal Items**: (none -- expository with inline formulas)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/sol (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/int, fol/byd/msl
- **OL Cross-refs**: (none)
- **Notes**: Substantial section covering: second-order syntax (relation variables, quantification), comprehension schema (predicative vs. impredicative), full vs. weak semantics, categoricity of second-order PA (with proof sketch), expressiveness (finiteness, well-orderings, connectedness), incompleteness of full second-order semantics, completeness for weak semantics via many-sorted embedding. References to DEF-SEM006 (categoricity) are implicit in the categoricity discussion. This is the most technically dense section in the beyond chapter.

---

### fol/byd/hol — Higher-Order Logic
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/higher-order-logic.tex`
- **Domain**: SYNTAX / SEMANTICS (extension)
- **Introduces**: (none from taxonomy)
- **References**: (none from core taxonomy directly)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/hol (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/sol
- **OL Cross-refs**: (none)
- **Notes**: Describes finite type theory: types ($\mathbb{N}$, $\sigma \to \tau$, $\sigma \times \tau$), terms (variables, 0, successor, recursion, application, lambda abstraction, pairing, projection), formulas, full vs. weak semantics. Mentions Church's simple theory of types. Notes full semantics is incomplete, weak semantics admits completeness. Brief mention of constructive/intuitionistic variants.

---

### fol/byd/il — Intuitionistic Logic
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/intuitionistic-logic.tex`
- **Domain**: DEDUCTION (alternative)
- **Introduces**: (none from taxonomy)
- **References**: (none from core taxonomy directly)
- **OL Formal Items**:
  - thm (unlabeled: equivalence of excluded middle schemata) -> OL-ONLY: TANGENTIAL
  - thm (unlabeled: double-negation translation -- classical provability implies intuitionistic provability of $A^N$) -> OL-ONLY: TANGENTIAL
  - thm (unlabeled: relativization to hypotheses $\Gamma^N \vdash A^N$) -> OL-ONLY: TANGENTIAL
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/il (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/int
- **OL Cross-refs**: (none)
- **Notes**: Covers: BHK interpretation, Curry-Howard isomorphism, double-negation translation (Godel-Gentzen), Kripke semantics for intuitionistic propositional logic (with formal forcing definition), historical notes (Kolmogorov, Glivenko, Heyting). Contains three theorems but none are labeled. The irrational-to-irrational-power example is a classic motivation for constructive mathematics.

---

### fol/byd/mod — Modal Logics
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/modal-logics.tex`
- **Domain**: DEDUCTION / SEMANTICS (extension)
- **Introduces**: (none from taxonomy)
- **References**: (none from core taxonomy directly)
- **OL Formal Items**: (none -- expository)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/mod (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/int
- **OL Cross-refs**: (none)
- **Notes**: Covers: $\Box$ and $\Diamond$ operators, Kripke semantics (possible worlds, accessibility relation), applications (provability logic, epistemic logic, temporal logic), axiom systems S4 and S5 with their accessibility-relation characterizations. Brief and survey-level.

---

### fol/byd/oth — Other Logics
- **File**: `/home/quode/projects/OpenLogic/content/first-order-logic/beyond/other-logics.tex`
- **Domain**: (meta-survey)
- **Introduces**: (none)
- **References**: (none)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: FOL=fol/byd/oth (only)
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: fol/byd/int
- **OL Cross-refs**: (none)
- **Notes**: One-page survey mentioning fuzzy logic, probabilistic logic, default/nonmonotonic logics, epistemic logics, causal logics, deontic logics. No formal content. Closes with a Leibniz reference.

---

## Batch 6: Incompleteness (content/incompleteness/) — 44 sections

## Chapter 1: Introduction to Incompleteness (`inc/int/`)
### inc/int/bgr -- Historical Background
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/introduction/historical-background.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: (none)
- **References**: PRIM-DED006 (Provability), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**: (none -- purely narrative)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none -- first section in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Pure historical narrative covering Aristotle through Godel. No formal definitions or theorems. Entirely pedagogical context-setting.

### inc/int/def -- Definitions
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/introduction/definitions.tex`
- **Domain**: INCOMPLETENESS (primary), SEMANTICS + DEDUCTION + COMPUTATION (secondary)
- **Introduces**: DEF-INC001 (Theory, as deductively closed set), DEF-INC002 (Standard Model of Arithmetic N), DEF-INC003 (True Arithmetic TA), DEF-INC004 (Axiomatized Theory), DEF-INC005 (Robinson's Q), DEF-INC006 (Peano Arithmetic PA), DEF-INC007 (Complete Theory), DEF-INC008 (Axiomatizable Theory), DEF-CMP009 (Representability of Functions), DEF-INC009 (Representability of Relations)
- **References**: PRIM-SEM012 (Theory of a Structure -- TA as Th(N)), PRIM-DED006 (Provability), PRIM-DED002 (Non-Logical Axiom), PRIM-CMP006 (Decidable Set), PRIM-CMP007 (Semi-Decidable/c.e.)
- **OL Formal Items**:
  - defn (theory) -> DEF-INC001
  - defn[def:standard-model] -> DEF-INC002
  - defn (true arithmetic) -> DEF-INC003 (instantiates PRIM-SEM012)
  - defn (axiomatized) -> DEF-INC004
  - defn (Q) -> DEF-INC005
  - defn (PA, induction schema) -> DEF-INC006
  - defn (complete) -> DEF-INC007
  - defn (decidable set) -> references PRIM-CMP006
  - defn (axiomatizable) -> DEF-INC008
  - defn (c.e.) -> references PRIM-CMP007
  - defn (represents function) -> DEF-CMP009
  - defn (represents relation) -> DEF-INC009
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: inc/int/bgr
- **OL Cross-refs**: (none)
- **Notes**: This is a definition-dense section. DEF-CMP009 (Representability) is likely first formally defined here. The definitions of Q (DEF-INC005) and PA (DEF-INC006) are critical for all incompleteness results. PRIM-SEM012 is instantiated via TA = Th(N). Several new taxonomy IDs are needed for the incompleteness domain (INC001-INC009).

### inc/int/ovr -- Overview of Incompleteness Results
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/introduction/overview.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: (none -- previews but does not prove)
- **References**: CP-005 (First Incompleteness -- stated informally), CP-006 (Second Incompleteness -- previewed), DEF-CMP009 (Representability), PRIM-CMP011 (Godel Numbering -- previewed), DEF-INC007 (Complete Theory), DEF-INC008 (Axiomatizable)
- **OL Formal Items**:
  - thm (informal statement of first incompleteness) -> CP-005 preview (OL-ONLY: pedagogical)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: inc/int/def
- **OL Cross-refs**: (none)
- **Notes**: Roadmap section. States the first and second incompleteness theorems informally and explains the plan for proving them. No proofs.

### inc/int/dec -- Undecidability and Incompleteness
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/introduction/undecidability.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new -- but proves a "weak" version of incompleteness via diagonalization)
- **References**: DEF-CMP009 (Representability), PRIM-CMP006 (Decidable Set), DEF-INC007 (Complete Theory), DEF-INC008 (Axiomatizable), PRIM-CMP010 (Diagonalization), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - thm (consistent theory representing all decidable relations is not decidable) -> OL-ONLY: stepping stone for CP-005
  - thm (axiomatizable + complete => decidable) -> OL-ONLY: stepping stone for CP-005
  - cor[cor:incompleteness] (consistent + axiomatizable + represents all decidable properties => not complete) -> OL-ONLY: "weak first incompleteness" -- stepping stone for CP-005
  - prob (TA not axiomatizable) -> OL-ONLY: pedagogical
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/int/def
- **OL Cross-refs**: (none)
- **Notes**: Proves a weak version of the first incompleteness theorem using a diagonal argument. This does not construct an explicit independent sentence (that comes from arithmetization). Also proves that axiomatizable + complete implies decidable. Mentions Presburger arithmetic as a decidable theory.

---

## Chapter 2: Arithmetization of Syntax (`inc/art/`)

### inc/art/int -- Introduction (Arithmetization)
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/introduction.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none -- motivational)
- **References**: PRIM-CMP011 (Godel Numbering)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Motivates arithmetization of syntax. Explains the idea of coding symbols and sequences as numbers. Mentions Tarski and Godel limitative results as downstream applications.

### inc/art/cod -- Coding Symbols
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/coding-symbols.tex`
- **Domain**: INCOMPLETENESS (primary), SYNTAX + COMPUTATION (secondary)
- **Introduces**: DEF-INC010 (Symbol Code), DEF-INC011 (Godel Number of symbol sequence)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-CMP001 (Computable Function -- primitive recursive)
- **OL Formal Items**:
  - defn (symbol code) -> DEF-INC010
  - prop (Fn, Pred primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - defn (Godel number) -> DEF-INC011 (instantiates PRIM-CMP011)
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/int
- **OL Cross-refs**: (none)
- **Notes**: Assigns codes to logical symbols, variables, constants, functions, predicates. Defines Godel numbers as codes of sequences of symbol codes via power-of-primes.

### inc/art/trm -- Coding Terms
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/coding-terms.tex`
- **Domain**: INCOMPLETENESS (primary), SYNTAX + COMPUTATION (secondary)
- **Introduces**: (none new taxonomy items)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - prop[prop:term-primrec] (Term(x) and ClTerm(x) are primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:num-primrec] (num(n) is primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/cod
- **OL Cross-refs**: (none)
- **Notes**: Shows that the property of being a Godel number of a term is primitive recursive. Formation sequences provide the inductive structure.

### inc/art/frm -- Coding Formulas
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/coding-formulas.tex`
- **Domain**: INCOMPLETENESS (primary), SYNTAX + COMPUTATION (secondary)
- **Introduces**: (none new taxonomy items)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - prop (Atom(x) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:frm-primrec] (Frm(x) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:freeocc-primrec] (FreeOcc primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop (Sent(x) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
- **Role**: PROVE
- **Variant Tags**: prvFalse, prvTrue (for atomic formula cases)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/trm
- **OL Cross-refs**: `\olref[inc][art][trm]{prop:term-primrec}`
- **Notes**: Extends primitive recursiveness results to formulas and sentences.

### inc/art/sub -- Substitution
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/substitution.tex`
- **Domain**: INCOMPLETENESS (primary), SYNTAX + COMPUTATION (secondary)
- **Introduces**: (none new taxonomy items)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - prop[prop:subst-primrec] (Subst(x,y,z) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:free-for] (FreeFor primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/frm
- **OL Cross-refs**: (none)
- **Notes**: Shows that the substitution operation on Godel numbers is primitive recursive.

### inc/art/plk -- Derivations in LK
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/proofs-in-lk.tex`
- **Domain**: INCOMPLETENESS (primary), DEDUCTION + COMPUTATION (secondary)
- **Introduces**: DEF-INC012 (Prf_Gamma(x,y) -- proof predicate, LK variant)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-DED006 (Provability), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - defn (Godel number of derivation in LK) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:followsby] (Correct(p) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:deriv] (Deriv(p) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop (Prf_Gamma(x,y) primitive recursive) -> DEF-INC012
- **Role**: PROVE
- **Variant Tags**: prfSC
- **Dual ID**: inc/art/pnd, inc/art/pax
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/sub
- **OL Cross-refs**: (none)
- **Notes**: LK variant of coding derivations. Shows that the proof predicate Prf(x,y) is primitive recursive. This is the crucial bridge between syntax and computation needed for the incompleteness theorems.

### inc/art/pnd -- Derivations in Natural Deduction
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/proofs-in-nd.tex`
- **Domain**: INCOMPLETENESS (primary), DEDUCTION + COMPUTATION (secondary)
- **Introduces**: DEF-INC012 (Prf_Gamma(x,y) -- proof predicate, ND variant)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-DED006 (Provability), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - defn (Godel number of derivation in ND) -> OL-ONLY: stepping stone for CP-005/006
  - prop (Assum, Discharge primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:followsby] (Correct(d) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:deriv] (Deriv(d) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:openassum] (OpenAssum(z,d) primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:prf-prim-rec] (Prf_Gamma(x,y) primitive recursive) -> DEF-INC012
- **Role**: PROVE
- **Variant Tags**: prfND
- **Dual ID**: inc/art/plk, inc/art/pax
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/sub
- **OL Cross-refs**: `\olref[cmp][rec][tre]{sec}`
- **Notes**: Natural deduction variant of coding derivations. Parallel to inc/art/plk.

### inc/art/pax -- Axiomatic Derivations
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/arithmetization-syntax/proofs-in-ax.tex`
- **Domain**: INCOMPLETENESS (primary), DEDUCTION + COMPUTATION (secondary)
- **Introduces**: DEF-INC012 (Prf_Gamma(x,y) -- proof predicate, AX variant)
- **References**: PRIM-CMP011 (Godel Numbering), PRIM-DED006 (Provability), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - defn (Godel number of axiomatic derivation) -> OL-ONLY: stepping stone for CP-005/006
  - prop[prop:followsby] (IsAx, MP, QR, Deriv primitive recursive) -> OL-ONLY: stepping stone for CP-005/006
  - prop (Prf_Gamma(x,y) primitive recursive) -> DEF-INC012
- **Role**: PROVE
- **Variant Tags**: prfAX
- **Dual ID**: inc/art/plk, inc/art/pnd
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/art/sub
- **OL Cross-refs**: (none)
- **Notes**: Axiomatic derivation variant of coding derivations. Parallel to inc/art/plk and inc/art/pnd.

---

## Chapter 3: Representability in Q (`inc/req/`)

### inc/req/int -- Introduction (Representability)
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/introduction.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new -- restates DEF-CMP009, DEF-INC005)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Robinson's Q), DEF-INC006 (PA), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - defn[defn:representable-fn] (representable in Q) -> restates DEF-CMP009
  - thm[thm:representable-iff-comp] (representable in Q iff computable) -> OL-ONLY: core theorem stated, proved across chapter
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Restates Q axioms and the definition of representability. Announces the main theorem: representable iff computable. Outlines strategy using composition and regular minimization instead of primitive recursion.

### inc/req/rpc -- Functions Representable in Q are Computable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/representable-comp.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-CMP009 (Representability), PRIM-CMP011 (Godel Numbering), DEF-INC005 (Q), PRIM-CMP001 (Computable Function), DEF-INC012 (Proof predicate)
- **OL Formal Items**:
  - lem[lem:rep-q] (Q proves A_f(n,m) iff m=f(n)) -> OL-ONLY: stepping stone
  - lem (every representable function is computable) -> OL-ONLY: stepping stone for representability theorem
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/int
- **OL Cross-refs**: `\olref[int]{defn:representable-fn}`, `\olref[bre]{lem:q-proves-neq}`, `\olref[art][trm]{prop:num-primrec}`, `\olref[art][sub]{prop:subst-primrec}`
- **Notes**: Shows one direction: if f is representable in Q, then f is computable. Uses the proof predicate and Godel numbering to define f by minimization.

### inc/req/bet -- The Beta Function Lemma
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/beta-function.tex`
- **Domain**: COMPUTATION (primary), INCOMPLETENESS (secondary)
- **Introduces**: DEF-INC013 (Beta function)
- **References**: PRIM-CMP001 (Computable Function), PRIM-CMP010 (Diagonalization -- in the encoding sense)
- **OL Formal Items**:
  - lem[lem:beta] (beta function lemma) -> DEF-INC013
  - thm (Sunzi's/Chinese Remainder Theorem) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: (none)
- **Notes**: The beta function lemma is a key technical tool for simulating primitive recursion using only composition and minimization. Uses the Chinese Remainder Theorem. This is Godel's original method for handling sequences.

### inc/req/pri -- Simulating Primitive Recursion
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/prim-rec.tex`
- **Domain**: COMPUTATION (primary), INCOMPLETENESS (secondary)
- **Introduces**: (none new)
- **References**: DEF-INC013 (Beta function), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - lem[lem:prim-rec] (primitive recursion reducible to composition + regular minimization) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/bet
- **OL Cross-refs**: `\olref[bet]{lem:beta}`
- **Notes**: Shows that primitive recursion can be simulated by composition and regular minimization using the beta function. This is why we can avoid showing closure of representable functions under primitive recursion.

### inc/req/bre -- Basic Functions are Representable in Q
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/basic-representable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new taxonomy items)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q)
- **OL Formal Items**:
  - prop[prop:rep-zero] (Zero representable) -> OL-ONLY: stepping stone
  - prop[prop:rep-succ] (Succ representable) -> OL-ONLY: stepping stone
  - prop[prop:rep-proj] (Projection representable) -> OL-ONLY: stepping stone
  - prop[prop:rep-id] (Char= representable) -> OL-ONLY: stepping stone
  - lem[lem:q-proves-neq] (Q proves numerals distinct) -> OL-ONLY: stepping stone
  - prop[prop:rep-add] (Add representable) -> OL-ONLY: stepping stone
  - lem[lem:q-proves-add] (Q proves numeral addition) -> OL-ONLY: stepping stone
  - prop[prop:rep-mult] (Mult representable) -> OL-ONLY: stepping stone
  - lem[lem:q-proves-mult] (Q proves numeral multiplication) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/int
- **OL Cross-refs**: (none)
- **Notes**: Shows that Zero, Succ, projections, Char=, Add, Mult are all representable in Q. These are the base cases for the representability theorem.

### inc/req/cmp -- Composition is Representable in Q
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/composition-representable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q)
- **OL Formal Items**:
  - prop[prop:rep-composition] (representable functions closed under composition) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/bre
- **OL Cross-refs**: (none)
- **Notes**: Shows that if f and g_i are representable, then h defined by composition is representable.

### inc/req/min -- Regular Minimization is Representable in Q
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/minimization-representable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q)
- **OL Formal Items**:
  - lem[lem:succ] (Q proves a'+n = (a+n)') -> OL-ONLY: stepping stone
  - lem[lem:less-zero] (Q proves not x < 0) -> OL-ONLY: stepping stone
  - lem[lem:less-nsucc] (Q proves x < n+1 implies disjunction of equalities) -> OL-ONLY: stepping stone
  - lem[lem:trichotomy] (Q proves trichotomy for numerals) -> OL-ONLY: stepping stone
  - prop[prop:rep-minimization] (representable functions closed under regular minimization) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/bre, inc/req/cmp
- **OL Cross-refs**: (none)
- **Notes**: Shows closure under regular minimization. Requires several technical lemmas about what Q can prove about ordering of numerals.

### inc/req/crq -- Computable Functions are Representable in Q
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/comp-representable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new -- but completes the proof of the representability theorem)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q), PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - thm (every computable function is representable in Q) -> OL-ONLY: key theorem, stepping stone for CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/req/pri, inc/req/bre, inc/req/cmp, inc/req/min
- **OL Cross-refs**: multiple back-references to props in bre, cmp, min, pri
- **Notes**: Assembles all previous results. This completes the "computable implies representable" direction. Together with inc/req/rpc, establishes the representability theorem (representable iff computable).

### inc/req/cee -- The Functions C
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/c.tex`
- **Domain**: COMPUTATION
- **Introduces**: DEF-INC014 (Class C of functions)
- **References**: PRIM-CMP001 (Computable Function)
- **OL Formal Items**:
  - (informal definition of class C) -> DEF-INC014
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: inc/req/cre (the variant proof path using C)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Defines the class C of functions (zero, succ, add, mult, proj, Char=, closed under composition and regular minimization). This is an alternative approach to representing computable functions without directly handling primitive recursion closure.

### inc/req/cre -- Functions in C are Representable in Q
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/c-representable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q), DEF-INC014 (Class C)
- **OL Formal Items**:
  - lem (Q proves numerals distinct) -> duplicate of inc/req/bre content
  - (representability of basic functions and closure under composition/minimization) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: inc/req/crq (alternate presentation)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/cee
- **OL Cross-refs**: (none)
- **Notes**: This is an alternate, self-contained presentation that proves representability of all functions in C. Duplicates material from inc/req/bre and others. Includes the same explanation paragraph about computable = representable found in inc/req/crq.

### inc/req/rel -- Representing Relations
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/representing-relations.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new -- extends DEF-INC009 with full proof)
- **References**: DEF-INC009 (Representability of Relations), DEF-CMP009 (Representability of Functions), DEF-INC005 (Q)
- **OL Formal Items**:
  - defn[defn:representing-relations] (representable relation) -> restates DEF-INC009
  - thm[thm:representing-rels] (relation representable iff computable) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/req/crq (or inc/req/cre)
- **OL Cross-refs**: `\olref[int]{thm:representable-iff-comp}`
- **Notes**: Extends the representability theorem from functions to relations.

### inc/req/und -- Undecidability
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/undecidability.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: CP-008 (Church's Undecidability of Validity -- via corollary)
- **References**: DEF-INC005 (Q), PRIM-CMP006 (Decidable Set), DEF-INC012 (Proof predicate)
- **OL Formal Items**:
  - thm (Q is undecidable) -> OL-ONLY: stepping stone for CP-008
  - cor (first-order logic is undecidable) -> CP-008
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/req/rel
- **OL Cross-refs**: `\olref[cmp][rec][hlt]{thm:halting-problem}`, `\olref[cmp][rec][nft]{thm:kleene-nf}`
- **Notes**: Proves undecidability of Q by reduction from the halting problem. The corollary that first-order logic is undecidable is CP-008 (Church's Undecidability of Validity). Uses omega-consistency of Q (which follows from soundness).

### inc/inp/s1c -- Sigma-1 Completeness
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/representability-in-q/sigma1-completeness.tex`
- **Domain**: INCOMPLETENESS (primary), METATHEORY (secondary)
- **Introduces**: DEF-INC015 (Delta_0 formula), DEF-INC016 (Sigma_1 formula), DEF-INC017 (Pi_1 formula)
- **References**: DEF-INC005 (Q), DEF-INC002 (Standard Model N)
- **OL Formal Items**:
  - defn[defn:bd-quant] (bounded quantifiers) -> OL-ONLY: stepping stone
  - defn[defn:delta0-sigma1-pi1-frm] (Delta_0, Sigma_1, Pi_1 formulas) -> DEF-INC015, DEF-INC016, DEF-INC017
  - lem[lem:q-proves-clterm-id] (Q proves closed term identities) -> OL-ONLY: stepping stone
  - lem[lem:atomic-completeness] (atomic completeness) -> OL-ONLY: stepping stone
  - lem[lem:bounded-quant-equiv] (bounded quantifier equivalences) -> OL-ONLY: stepping stone
  - lem[lem:delta0-completeness] (Delta_0 completeness) -> OL-ONLY: stepping stone
  - thm[thm:sigma1-completeness] (Sigma_1 completeness of Q) -> OL-ONLY: CORE-THM (key for incompleteness)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/req/bre (for lemmas about Q)
- **OL Cross-refs**: `\olref[inc][req][bre]{lem:q-proves-add}`, `\olref[inc][req][bre]{lem:q-proves-mult}`, `\olref[inc][req][min]{lem:less-zero}`, `\olref[inc][req][min]{lem:less-nsucc}`
- **Notes**: The olfileid is inc/inp/s1c (suggesting it was originally in the incompleteness-provability chapter) but the file lives in representability-in-q/. Sigma_1-completeness is a crucial result: Q proves all true Sigma_1 sentences. This strengthens the representability results and is used in the incompleteness proofs.

---

## Chapter 4: Theories and Computability (`inc/tcp/`)

### inc/tcp/int -- Introduction (Theories and Computability)
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/introduction.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none)
- **References**: DEF-CMP009 (Representability), DEF-INC005 (Q), PRIM-CMP011 (Godel Numbering)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: `\olref[req][int]{defn:representable-fn}`, `\olref[req][rel]{defn:representing-relations}`, `\olref[req][int]{thm:representable-iff-comp}`, `\olref[req][rel]{thm:representing-rels}`
- **Notes**: Brief intro summarizing what has been established. Marked as needing rewrite in editorial comment.

### inc/tcp/qce -- Q is c.e.-Complete
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/q-is-ce.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-INC005 (Q), PRIM-CMP007 (Semi-Decidable/c.e.), PRIM-CMP006 (Decidable Set), DEF-INC012 (Proof predicate)
- **OL Formal Items**:
  - thm (Q is c.e.-complete) -> OL-ONLY: stepping stone for CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/int
- **OL Cross-refs**: (none)
- **Notes**: Shows Q is c.e. but not decidable, and in fact c.e.-complete (K reduces to Q). Uses Kleene's T predicate.

### inc/tcp/oqn -- Omega-Consistent Extensions of Q are Undecidable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/oconsis-ext-of-q-undec.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: DEF-INC018 (Omega-consistency -- first formal definition here in tcp chapter)
- **References**: DEF-INC005 (Q), PRIM-CMP006 (Decidable Set), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - defn[thm:oconsis-q] (omega-consistency) -> DEF-INC018
  - thm (omega-consistent extension of Q is not decidable) -> OL-ONLY: stepping stone for CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/qce
- **OL Cross-refs**: (none)
- **Notes**: Strengthens the c.e.-completeness result: omega-consistent extensions of Q are undecidable. Historical note: Godel's original result used omega-consistency.

### inc/tcp/cqn -- Consistent Extensions of Q are Undecidable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/extensions-of-q-not-decidable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-INC005 (Q), DEF-DED001 (Syntactic Consistency), PRIM-CMP006 (Decidable Set), PRIM-CMP010 (Diagonalization)
- **OL Formal Items**:
  - lem (no universal computable relation) -> OL-ONLY: stepping stone
  - thm (consistent extension of Q is not decidable) -> OL-ONLY: stepping stone for CP-005
  - cor (true arithmetic not decidable) -> OL-ONLY: stepping stone
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/oqn
- **OL Cross-refs**: `\olref[oqn]{thm:oconsis-q}`
- **Notes**: Strengthens the omega-consistency result to simple consistency. Uses the non-existence of a universal computable relation (a diagonalization argument).

### inc/tcp/cax -- Axiomatizable Theories
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/computably-axiomatizable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new -- restates DEF-INC008)
- **References**: DEF-INC008 (Axiomatizable), PRIM-CMP007 (Semi-Decidable/c.e.)
- **OL Formal Items**:
  - lem (axiomatizable implies c.e.) -> OL-ONLY: stepping stone for CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/int
- **OL Cross-refs**: (none)
- **Notes**: Short section establishing that axiomatizable theories are c.e.

### inc/tcp/cdc -- Axiomatizable Complete Theories are Decidable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/complete-decidable.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-INC007 (Complete Theory), DEF-INC008 (Axiomatizable), PRIM-CMP006 (Decidable Set), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - lem (complete + axiomatizable implies decidable) -> OL-ONLY: stepping stone for CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/cax
- **OL Cross-refs**: (none)
- **Notes**: Key connecting lemma: if T is complete, consistent, and axiomatizable, then T is decidable. Contrapositive: if T is undecidable, consistent, and axiomatizable, then T is incomplete.

### inc/tcp/inc -- Q has no Complete, Consistent, Axiomatizable Extensions
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/first-incompleteness.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: CP-005 (First Incompleteness Theorem -- computability-theoretic version)
- **References**: DEF-INC005 (Q), DEF-INC007 (Complete), DEF-INC008 (Axiomatizable), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - thm[thm:first-incompleteness] (no complete, consistent, axiomatizable extension of Q) -> CP-005 (computability-theoretic formulation)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: inc/inp/1in (the other formulation via Godel sentence)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/tcp/cqn, inc/tcp/cdc
- **OL Cross-refs**: (none)
- **Notes**: This is a version of the First Incompleteness Theorem proved via computability theory (undecidability of extensions of Q + complete+axiomatizable implies decidable). The proof is very short, combining the two preceding results. Compared to Godel's original proof, this version does not construct an explicit independent sentence.

### inc/tcp/ins -- Sentences Provable and Refutable in Q are Computably Inseparable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/inseparability.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: DEF-INC019 (Computable inseparability of Q and Q-bar)
- **References**: DEF-INC005 (Q), PRIM-CMP006 (Decidable Set), DEF-CMP009 (Representability), PRIM-CMP010 (Diagonalization)
- **OL Formal Items**:
  - lem (Q and Q-bar are computably inseparable) -> DEF-INC019
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/cqn
- **OL Cross-refs**: (none)
- **Notes**: Shows that the set of sentences provable in Q and the set refutable in Q are computably inseparable. Uses the non-existence of a universal computable relation.

### inc/tcp/con -- Theories Consistent with Q are Undecidable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/consis-with-q.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION (secondary)
- **Introduces**: (none new)
- **References**: DEF-INC005 (Q), DEF-DED001 (Syntactic Consistency), PRIM-CMP006 (Decidable Set), DEF-INC019 (Computable inseparability)
- **OL Formal Items**:
  - thm (theory consistent with Q is undecidable) -> OL-ONLY: strengthening of undecidability
  - cor (first-order logic for language of arithmetic is undecidable) -> CP-008 (alternative proof)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/ins
- **OL Cross-refs**: (none)
- **Notes**: Stronger than inc/tcp/cqn: the theory need not extend Q, only be consistent with it. Corollary gives another proof that first-order logic (for the language of arithmetic) is undecidable.

### inc/tcp/itp -- Theories in which Q is Interpretable are Undecidable
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/theories-computability/interpretability.tex`
- **Domain**: INCOMPLETENESS (primary), COMPUTATION + METATHEORY (secondary)
- **Introduces**: DEF-INC020 (Interpretability -- informal)
- **References**: DEF-INC005 (Q), PRIM-CMP006 (Decidable Set), DEF-DED001 (Syntactic Consistency)
- **OL Formal Items**:
  - thm (theory interpreting Q and consistent with it is undecidable) -> OL-ONLY: strongest undecidability result
  - cor (no decidable extension of ZFC) -> OL-ONLY: application
  - cor (no complete consistent axiomatizable extension of ZFC) -> OL-ONLY: application
  - cor (FOL for language with binary relation is undecidable) -> CP-008 (strongest form)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: inc/tcp/con
- **OL Cross-refs**: (none)
- **Notes**: The most general undecidability result. Informally introduces the notion of interpretability (not formally defined). Applications to ZFC and FOL with just a binary relation. Notes that FOL for unary predicates + at most one unary function is decidable (sharp boundary).

---

## Chapter 5: Incompleteness and Provability (`inc/inp/`)

### inc/inp/int -- Introduction (Incompleteness and Provability)
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/introduction.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: (none -- motivational)
- **References**: CP-005 (First Incompleteness -- previewed), CP-006 (Second Incompleteness -- previewed), DEF-INC005 (Q), PRIM-CMP010 (Diagonalization), PRIM-CMP011 (Godel Numbering)
- **OL Formal Items**:
  - lem (fixed-point lemma -- stated informally) -> preview of inc/inp/fix
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: (none in chapter)
- **OL Cross-refs**: (none)
- **Notes**: Motivates the Godel sentence construction via the Epimenides/liar paradox and Quine's version. Explains the self-referential idea and how diagonalization will be formalized.

### inc/inp/fix -- The Fixed-Point Lemma
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/fixed-point-lemma.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: DEF-INC021 (Fixed-Point Lemma / Diagonalization Lemma)
- **References**: DEF-INC005 (Q), DEF-CMP009 (Representability), PRIM-CMP010 (Diagonalization), PRIM-CMP011 (Godel Numbering)
- **OL Formal Items**:
  - lem[lem:fixed-point] (fixed-point lemma) -> DEF-INC021
  - prob (no truth definition -- quick Tarski via fixed point) -> references CP-007
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/int
- **OL Cross-refs**: (none)
- **Notes**: The fixed-point lemma (also called the diagonalization lemma or self-reference lemma) is the key technical tool for all the major incompleteness results. For any formula B(x), there is a sentence A such that Q proves A <-> B(gn(A)). The proof uses the diag function, which is primitive recursive and hence representable in Q.

### inc/inp/1in -- The First Incompleteness Theorem
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/first-incompleteness-thm.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: CP-005 (First Incompleteness Theorem -- Godel's version with omega-consistency)
- **References**: DEF-INC021 (Fixed-Point Lemma), DEF-INC005 (Q), DEF-INC012 (Proof predicate), DEF-DED001 (Syntactic Consistency), DEF-INC018 (Omega-consistency)
- **OL Formal Items**:
  - lem[lem:cons-G-unprov] (if T consistent, T does not derive G_T) -> OL-ONLY: stepping stone for CP-005
  - defn[thm:oconsis-q] (omega-consistency) -> restates DEF-INC018
  - lem[lem:omega-cons-G-unref] (if T omega-consistent, T does not derive not-G_T) -> OL-ONLY: stepping stone for CP-005
  - thm[thm:first-incompleteness] (First Incompleteness Theorem, omega-consistency version) -> CP-005
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: inc/tcp/inc (computability-theoretic version)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/fix
- **OL Cross-refs**: (none)
- **Notes**: This is Godel's original proof of the First Incompleteness Theorem. Constructs the Godel sentence G_T as a fixed point of "not Prov_T(x)". Shows G_T is independent of T assuming omega-consistency. The omega-consistency assumption is later weakened to consistency by Rosser's theorem.

### inc/inp/ros -- Rosser's Theorem
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/rosser-thm.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: DEF-INC022 (Rosser provability predicate), DEF-INC023 (Rosser sentence)
- **References**: CP-005 (First Incompleteness -- strengthened), DEF-INC021 (Fixed-Point Lemma), DEF-DED001 (Syntactic Consistency), DEF-INC012 (Proof predicate)
- **OL Formal Items**:
  - thm[thm:rosser] (Rosser's Theorem: consistent + axiomatizable + extends Q => incomplete) -> CP-005 (strengthened form)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/1in
- **OL Cross-refs**: `\olref[1in]{thm:first-incompleteness}`, `\olref[req][min]{lem:less-nsucc}`, `\olref[req][min]{lem:trichotomy}`
- **Notes**: Rosser's improvement of the First Incompleteness Theorem: replaces omega-consistency with simple consistency. Uses a modified "Rosser provability" predicate that includes a check for the absence of a shorter refutation. This is the standard modern form of CP-005.

### inc/inp/gop -- Comparison with Godel's Original Paper
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/godels-paper.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: (none)
- **References**: PRIM-CMP011 (Godel Numbering), DEF-INC013 (Beta function), DEF-INC005 (Q)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: inc/inp/1in
- **OL Cross-refs**: (none)
- **Notes**: Brief historical comparison with Godel's 1931 paper. Notes the 45 primitive recursive functions/relations, the beta-lemma, and the sketch of the second incompleteness theorem.

### inc/inp/prc -- The Derivability Conditions for PA
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/provability-conditions.tex`
- **Domain**: INCOMPLETENESS (primary), DEDUCTION (secondary)
- **Introduces**: DEF-INC024 (Hilbert-Bernays-Lob Derivability Conditions P1-P3)
- **References**: DEF-INC006 (PA), DEF-INC012 (Proof predicate), PRIM-DED006 (Provability)
- **OL Formal Items**:
  - (P1) If PA derives A, then PA derives Prov(gn(A)) -> part of DEF-INC024
  - (P2) PA derives Prov(gn(A->B)) -> (Prov(gn(A)) -> Prov(gn(B))) -> part of DEF-INC024
  - (P3) PA derives Prov(gn(A)) -> Prov(gn(Prov(gn(A)))) -> part of DEF-INC024
  - (P4) If PA derives Prov(gn(A)), then PA derives A -> mentioned but not needed
- **Role**: DEFINE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: inc/inp/1in
- **OL Cross-refs**: (none)
- **Notes**: Defines the three Hilbert-Bernays-Lob derivability conditions that are needed for the Second Incompleteness Theorem. Notes that P1 and P2 are easy to verify while P3 requires substantial work. The verification details are not carried out (following Godel's own practice).

### inc/inp/2in -- The Second Incompleteness Theorem
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/second-incompleteness-thm.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: CP-006 (Second Incompleteness Theorem)
- **References**: DEF-INC024 (Derivability Conditions), DEF-INC006 (PA), DEF-DED001 (Syntactic Consistency), PRIM-DED006 (Provability), DEF-INC021 (Fixed-Point Lemma)
- **OL Formal Items**:
  - thm[thm:second-incompleteness] (PA consistent => PA does not derive Con(PA)) -> CP-006
  - thm[thm:second-incompleteness-gen] (general version: T consistent + axiomatized + extends Q + P1-P3 => T does not derive Con(T)) -> CP-006 (generalized)
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/prc, inc/inp/1in
- **OL Cross-refs**: `\olref[1in]{thm:first-incompleteness}`
- **Notes**: The Second Incompleteness Theorem. The proof is a formalization within PA of the proof that "if T is consistent then T does not derive G_T." The key insight is that this argument can itself be formalized using the derivability conditions P1-P3. The consistency statement Con(T) is defined as not-Prov(gn(falsum)). Hilbert's program implications are discussed.

### inc/inp/lob -- Lob's Theorem
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/lob-thm.tex`
- **Domain**: INCOMPLETENESS
- **Introduces**: DEF-INC025 (Lob's Theorem)
- **References**: DEF-INC024 (Derivability Conditions), DEF-INC021 (Fixed-Point Lemma), CP-006 (Second Incompleteness -- derived as corollary)
- **OL Formal Items**:
  - thm[thm:lob] (Lob's Theorem: if T derives Prov(gn(A)) -> A, then T derives A) -> DEF-INC025
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/2in
- **OL Cross-refs**: `\olref[2in]{sec}`
- **Notes**: Lob's Theorem generalizes the Second Incompleteness Theorem. The proof uses the "Santa Claus" heuristic: applies the fixed-point lemma to Prov(y) -> A. The Second Incompleteness Theorem follows as a corollary (take A = falsum). Also shows that the fixed point of Prov(x) is derivable (unlike the Godel sentence, which is a fixed point of not-Prov(x)).

### inc/inp/tar -- The Undefinability of Truth
- **File**: `/home/quode/projects/OpenLogic/content/incompleteness/incompleteness-provability/tarski-thm.tex`
- **Domain**: INCOMPLETENESS (primary), SEMANTICS (secondary)
- **Introduces**: CP-007 (Tarski's Undefinability of Truth)
- **References**: DEF-INC002 (Standard Model N), DEF-INC003 (True Arithmetic), DEF-INC021 (Fixed-Point Lemma), DEF-CMP009 (Representability)
- **OL Formal Items**:
  - defn (definable in N) -> OL-ONLY: stepping stone for CP-007
  - lem (every computable relation is definable in N) -> OL-ONLY: stepping stone
  - lem (halting relation is definable in N) -> OL-ONLY: stepping stone
  - thm[thm:tarski] (set of true sentences of arithmetic is not definable) -> CP-007
- **Role**: PROVE
- **Variant Tags**: (none)
- **Dual ID**: (none)
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: inc/inp/fix
- **OL Cross-refs**: (none)
- **Notes**: Tarski's Undefinability of Truth theorem. Defines "definable in N" (equivalent to representable in TA). Shows that every computable relation is definable but the halting relation is also definable (so definability goes beyond computability). Then proves that the set of true sentences is NOT definable, using the fixed-point lemma to construct a liar sentence. Discusses Tarski's philosophical analysis of truth predicates.

---

## Batch 7: Set Theory (content/set-theory/) — 62 sections

---
## Chapter 1: story/ -- The Iterative Conception (6 sections)
### sth/story/extensionality -- Extensionality
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/extensionality.tex`
- **Domain**: SET
- **Introduces**: AX-SET001
- **References**: PRIM-SET002 (membership)
- **OL Formal Items**:
  - axiom[Extensionality] -> AX-SET001
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: none (first section in chapter)
- **OL Cross-refs**: olref[sfr][][]{part}
- **Notes**: This is the first formal axiom statement of ZFC in the text. It appears here in the narrative chapter, then is referenced throughout. The axiom is re-invoked in sth/z/milestone when defining Z^-.

---

### sth/story/rus -- Russell's Paradox (again)
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/russells-paradox-again.tex`
- **Domain**: SET
- **Introduces**: (none -- re-derives OL-ONLY: Russell's Paradox, restated from sfr)
- **References**: AX-SET001 (mentioned), PRIM-SET002
- **OL Formal Items**:
  - defish[Naive Comprehension] -> OL-ONLY (rejected principle)
  - thm[Russell's Paradox] -> OL-ONLY (re-proof from sfr)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/story/extensionality
- **OL Cross-refs**: olref[sfr][set][rus]{sec}, olref[story][blv]{sec}
- **Notes**: Historical motivation for restricting comprehension. The paradox is a theorem of pure logic.

---

### sth/story/predicative -- Predicative and Impredicative
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/predicativity.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: (none in taxonomy)
- **OL Formal Items**:
  - defish[Predicative Comprehension] -> OL-ONLY (informal principle)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/story/rus
- **OL Cross-refs**: olref[sth][story][rus]{sec}
- **Notes**: Philosophical discussion of predicativity vs impredicativity. Motivates cumulative approach. No formal definitions introduced that map to taxonomy.

---

### sth/story/approach -- The Cumulative-Iterative Approach
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/cumulative-approach.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- but introduces informal notion of "stages")
- **References**: (none in taxonomy)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/story/predicative
- **OL Cross-refs**: (none)
- **Notes**: Key conceptual section: introduces the cumulative-iterative conception of set. Explains informally how Russell's Paradox is avoided. No formal axioms, but underpins the entire formal development. The V_alpha hierarchy is later formalized in sth/spine/.

---

### sth/story/urelements -- Urelements or Not?
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/urelements.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: (none in taxonomy)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/story/approach
- **OL Cross-refs**: olref[story][approach]{sec}, olref[sfr][siz][]{chap}
- **Notes**: Design decision: the book excludes urelements. Purely motivational.

---

### sth/story/blv -- Appendix: Frege's Basic Law V
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/story/grundgesetze.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: (none in taxonomy)
- **OL Formal Items**:
  - lem[Fregeextensions] -> OL-ONLY (historical)
  - lem (Naive Comprehension from BLV) -> OL-ONLY (historical)
- **Role**: DISCUSS
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: sth/story/rus
- **OL Cross-refs**: olref[rus]{sec}
- **Notes**: Historical appendix on Frege's system. Shows how Basic Law V yields Naive Comprehension and then Russell's Paradox.

---

## Chapter 2: z/ -- Steps towards Z (8 sections)

### sth/z/story -- The Story in More Detail
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/story.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- introduces informal principles StagesHier, StagesOrd, StagesAcc)
- **References**: (none in taxonomy)
- **OL Formal Items**: (none formal -- informal enumerated principles)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/story/approach
- **OL Cross-refs**: olref[story][approach]{sec}
- **Notes**: Spells out three informal principles about the cumulative hierarchy (StagesHier, StagesOrd, StagesAcc) that justify the axioms of Z. These are used informally throughout the chapter.

---

### sth/z/sep -- Separation
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/separation.tex`
- **Domain**: SET
- **Introduces**: AX-SET006, AX-SET002 (as consequence)
- **References**: AX-SET001 (Extensionality, used in proofs), PRIM-SET002
- **OL Formal Items**:
  - axiom[Scheme of Separation] -> AX-SET006
  - thm[NoUniversalSet] -> OL-ONLY (consequence of Separation)
  - prop[emptyexists] -> AX-SET002 (derives empty set existence from Separation)
  - prop (A\B exists) -> OL-ONLY (technical)
  - prop[intersectionsexist] -> OL-ONLY (technical consequence)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/story/extensionality, sth/z/story
- **OL Cross-refs**: (none external)
- **Notes**: Defines the Separation scheme (AX-SET006). Also derives the empty set (AX-SET002 as consequence, not independent axiom). The no-universal-set theorem is a key consequence.

---

### sth/z/union -- Union
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/union.tex`
- **Domain**: SET
- **Introduces**: AX-SET004
- **References**: AX-SET006 (Separation, for intersections), PRIM-SET002
- **OL Formal Items**:
  - axiom[Union] -> AX-SET004
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/z/sep
- **OL Cross-refs**: olref[sth][z][sep]{prop:intersectionsexist}
- **Notes**: Defines the Union axiom (AX-SET004), justified via cumulative-iterative conception.

---

### sth/z/pairs -- Pairs
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/pairs.tex`
- **Domain**: SET
- **Introduces**: AX-SET003
- **References**: AX-SET001 (Extensionality), AX-SET004 (Union), PRIM-SET002
- **OL Formal Items**:
  - axiom[Pairs] -> AX-SET003
  - prop[pairsconsequences] -> OL-ONLY (singletons, binary union, ordered pairs as consequences)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/z/union
- **OL Cross-refs**: (none external)
- **Notes**: Defines Pairing axiom. Also introduces StagesSucc (no last stage). Proves existence of singletons, binary union, and ordered pairs.

---

### sth/z/power -- Powersets
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/powerset.tex`
- **Domain**: SET
- **Introduces**: AX-SET005
- **References**: AX-SET003 (Pairs), AX-SET006 (Separation), PRIM-SET002
- **OL Formal Items**:
  - axiom[Powersets] -> AX-SET005
  - prop[thm:Products] -> OL-ONLY (Cartesian product existence)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/z/pairs
- **OL Cross-refs**: olref[sth][z][pairs]{prop:pairsconsequences}
- **Notes**: Defines Power Set axiom (AX-SET005). Proves Cartesian product existence as consequence of Powerset + Separation.

---

### sth/z/infinity-again -- Infinity
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/infinity-again.tex`
- **Domain**: SET
- **Introduces**: AX-SET008
- **References**: AX-SET006 (Separation), AX-SET003 (Pairs), PRIM-SET002
- **OL Formal Items**:
  - axiom[Infinity] -> AX-SET008
  - defn[defnomega] -> OL-ONLY (defines omega as closure of successor starting from emptyset)
  - prop[naturalnumbersarentinfinite] -> OL-ONLY (no natural number is Dedekind infinite)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/z/power
- **OL Cross-refs**: olref[sfr][infinite][dedekind]{thm:DedekindInfiniteAlgebra}, olref[sth][z][nat]{sec}
- **Notes**: Defines the Axiom of Infinity (AX-SET008). Also defines omega and natural numbers. Introduces StagesInf (informal principle about infinite stages).

---

### sth/z/milestone -- Z^-: a Milestone
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/milestone.tex`
- **Domain**: SET
- **Introduces**: (none new -- defines theory Z^-)
- **References**: AX-SET001, AX-SET003, AX-SET004, AX-SET005, AX-SET006, AX-SET008
- **OL Formal Items**:
  - defn (Z^-) -> OL-ONLY (collects axioms into named theory)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/z/infinity-again
- **OL Cross-refs**: olref[sfr][][]{part}, olref[sth][z][arbintersections]{sec}
- **Notes**: Milestone section collecting all axioms of Zermelo set theory minus Foundation. No new formal content.

---

### sth/z/nat -- Selecting our Natural Numbers
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/nat.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET008 (Infinity)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/z/infinity-again
- **OL Cross-refs**: olref[sfr][rel][ref]{sec}, olref[sfr][arith][ref]{sec}, olref[sfr][infinite][dedekindsproof]{sec}, olref[ordinals][]{chap}
- **Notes**: Philosophical discussion of Benacerraf's problem: which sets are the natural numbers? Von Neumann vs Zermelo approach.

---

### sth/z/arbintersections -- Appendix: Closure, Comprehension, and Intersection
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/z/arbintersections.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET001 (Extensionality), AX-SET006 (Separation)
- **OL Formal Items**: (none labeled)
- **Role**: APPLY
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/z/milestone
- **OL Cross-refs**: olref[sth][z][milestone]{sec}, olref[sth][z][sep]{prop:intersectionsexist}, olref[sfr][infinite][dedekind]{Closure}
- **Notes**: Technical appendix showing how to define intersections via Separation rather than Naive Comprehension. Demonstrates that closure definitions from sfr/ are legitimate in Z^-.

---

## Chapter 3: ordinals/ -- Ordinals (9 sections)

### sth/ordinals/intro -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/introduction.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET008 (Infinity)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/z/ (all)
- **OL Cross-refs**: olref[z][]{chap}
- **Notes**: Brief motivational introduction to the ordinals chapter.

---

### sth/ordinals/idea -- The General Idea of an Ordinal
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/idea.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- informal notion of order types)
- **References**: (none in taxonomy)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/ordinals/intro
- **OL Cross-refs**: (none)
- **Notes**: Informal examples of omega, omega+1, omega+omega orderings on natural numbers. Motivates formal treatment.

---

### sth/ordinals/wo -- Well-Orderings
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/wo.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-well-ordering (well-order definition)
- **References**: PRIM-SET002
- **OL Formal Items**:
  - defn (well-ordering) -> OL-ONLY (definition of well-ordering)
  - prop[wo:strictorder] -> OL-ONLY (unique least element, irreflexive, etc.)
  - prop[propwoinduction] -> DEF-SET006 (strong induction on well-orderings -- this is the core of transfinite induction)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/ordinals/idea
- **OL Cross-refs**: (none external)
- **Notes**: Defines well-orderings formally. The induction principle (propwoinduction) is the kernel of DEF-SET006 (Transfinite Induction), though the full definition comes in sth/ordinals/basic.

---

### sth/ordinals/iso -- Order-Isomorphisms
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/iso.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-order-isomorphism, DEF-initial-segment
- **References**: PRIM-SET002
- **OL Formal Items**:
  - defn (order-isomorphism) -> OL-ONLY
  - lem[isoscompose] -> OL-ONLY
  - cor[ordisoisequiv] -> OL-ONLY
  - prop[ordisounique] -> OL-ONLY (uniqueness of isomorphisms between well-orderings)
  - defn (initial segment A_a) -> OL-ONLY
  - lem[wellordnotinitial] -> OL-ONLY (no well-ordering isomorphic to proper initial segment)
  - lem[wellordinitialsegment] -> OL-ONLY
  - lem[lemordsegments] -> OL-ONLY
  - thm[thm:woalwayscomparable] -> OL-ONLY (well-orderings are always comparable)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ordinals/wo
- **OL Cross-refs**: olref[wo]{propwoinduction}
- **Notes**: Extensive technical development of order-isomorphism theory. Key result: well-orderings are always comparable (thm:woalwayscomparable). This section supports the ordinal representation theorem.

---

### sth/ordinals/vn -- Von Neumann's Construction of the Ordinals
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/vn.tex`
- **Domain**: SET
- **Introduces**: DEF-SET001, DEF-SET002, DEF-SET003
- **References**: PRIM-SET002
- **OL Formal Items**:
  - defn (transitive set, ordinal = transitive + well-ordered by membership) -> DEF-SET001 (Ordinal), DEF-SET002 (Transitive Set), DEF-SET003 (Von Neumann Ordinal)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/ordinals/iso
- **OL Cross-refs**: olref[sth][ordinals][iso]{thm:woalwayscomparable}, olref[sth][z][infinity-again]{sec}
- **Notes**: Defines the key notions: transitive set (DEF-SET002), ordinal as transitive set well-ordered by membership (DEF-SET001/DEF-SET003). Shows first few ordinals are the natural numbers.

---

### sth/ordinals/basic -- Basic Properties of the Ordinals
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/basic.tex`
- **Domain**: SET
- **Introduces**: DEF-SET006 (Transfinite Induction -- full statement), PRIM-SET003 (Proper Class -- via Burali-Forti Paradox)
- **References**: DEF-SET001, DEF-SET002, DEF-SET003
- **OL Formal Items**:
  - lem[ordmemberord] -> OL-ONLY (element of ordinal is ordinal)
  - cor[ordissetofsmallerord] -> OL-ONLY
  - thm[ordinductionschema] (Transfinite Induction) -> DEF-SET006
  - thm[ordtrichotomy] (Trichotomy) -> OL-ONLY (ordinals are trichotomous)
  - cor[ordordered] -> OL-ONLY
  - cor[corordtransitiveord] -> OL-ONLY (A is ordinal iff transitive set of ordinals)
  - thm[buraliforti] (Burali-Forti Paradox) -> PRIM-SET003 (no set of all ordinals -- implies proper class)
  - prop (no infinite descending chain) -> OL-ONLY
  - prop[ordinalsaresubsets] -> OL-ONLY
  - prop[ordisoidentity] -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: sth/ordinals/vn
- **OL Cross-refs**: olref[iso]{wellordnotinitial}, olref[wo]{wo:strictorder}
- **Notes**: Central section establishing transfinite induction (DEF-SET006), trichotomy, and the Burali-Forti Paradox (which witnesses PRIM-SET003, the concept of proper class). The ordinals are collectively well-ordered by membership but do not form a set.

---

### sth/ordinals/replacement -- Replacement
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/replacement.tex`
- **Domain**: SET
- **Introduces**: AX-SET007
- **References**: AX-SET006 (Separation), DEF-SET001
- **OL Formal Items**:
  - axiom[Scheme of Replacement] -> AX-SET007
  - cor (image of set under term exists) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/ordinals/basic
- **OL Cross-refs**: olref[sth][replacement][]{chap}, olref[replacement][strength]{sec}
- **Notes**: Defines the Replacement axiom scheme (AX-SET007). Motivated by the need to prove every well-ordering is isomorphic to an ordinal.

---

### sth/ordinals/zfm -- ZF^-: a milestone
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/milestone.tex`
- **Domain**: SET
- **Introduces**: (none new -- defines theory ZF^-)
- **References**: AX-SET001, AX-SET003, AX-SET004, AX-SET005, AX-SET006, AX-SET007, AX-SET008
- **OL Formal Items**:
  - defn (ZF^-) -> OL-ONLY (collects axioms into named theory)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ordinals/replacement
- **OL Cross-refs**: olref[replacement][]{chap}
- **Notes**: Milestone section: ZF^- = Z^- + Replacement.

---

### sth/ordinals/ordtype -- Ordinals as Order-Types
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/ordtype.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-order-type
- **References**: AX-SET007 (Replacement), DEF-SET001
- **OL Formal Items**:
  - thm[thmOrdinalRepresentation] -> OL-ONLY (every well-ordering isomorphic to unique ordinal -- key representation theorem)
  - defn (order type ordtype(A,<)) -> OL-ONLY
  - cor[ordtypesworklikeyouwant] -> OL-ONLY (order types behave correctly)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: sth/ordinals/replacement
- **OL Cross-refs**: olref[basic]{ordisoidentity}, olref[iso]{lemordsegments}, olref[iso]{wellordinitialsegment}
- **Notes**: Proves the Ordinal Representation Theorem: every well-ordering is isomorphic to a unique ordinal. Requires Replacement. This is a major theorem supporting the ordinal theory.

---

### sth/ordinals/opps -- Successor and Limit Ordinals
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ordinals/opps.tex`
- **Domain**: SET
- **Introduces**: DEF-SET004, DEF-SET005
- **References**: DEF-SET001, DEF-SET006
- **OL Formal Items**:
  - defn (successor ordinal, limit ordinal) -> DEF-SET004, DEF-SET005
  - thm[simpletransrecursion] (Simple Transfinite Induction) -> OL-ONLY (variant of DEF-SET006 for successor/limit cases)
  - defn[defsupstrict] (lsub/supstrict) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/ordinals/basic
- **OL Cross-refs**: olref[basic]{corordtransitiveord}, olref[basic]{ordordered}
- **Notes**: Defines successor ordinals (DEF-SET004) and limit ordinals (DEF-SET005). Also provides Simple Transfinite Induction (base/successor/limit case variant).

---

## Chapter 4: spine/ -- Stages and Ranks (6 sections)

### sth/spine/valpha -- Defining the Stages as the V_alpha's
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/idea.tex`
- **Domain**: SET
- **Introduces**: DEF-SET012 (Von Neumann Hierarchy) [Phase 2.5: upgraded from OL-ONLY]
- **References**: DEF-SET001, DEF-SET004, DEF-SET005, AX-SET005 (Powerset)
- **OL Formal Items**:
  - defn[defValphas] (V_alpha definition by transfinite recursion) -> DEF-SET012 [Phase 2.5: was OL-ONLY]
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/ordinals/ (all), sth/spine/recursion (logically)
- **OL Cross-refs**: olref[sth][ordinals][]{chap}, olref[sth][ordinals][opps]{sec}
- **Notes**: Defines the cumulative hierarchy V_alpha by transfinite recursion. This is the formal realization of the informal "stages" notion from sth/story/approach. The definition requires the Transfinite Recursion Theorem proved in the next section.

---

### sth/spine/recursion -- The Transfinite Recursion Theorem(s)
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/recursion.tex`
- **Domain**: SET
- **Introduces**: DEF-SET007, THM-SET002 (Transfinite Recursion Theorem)
- **References**: DEF-SET006 (Transfinite Induction), AX-SET007 (Replacement)
- **OL Formal Items**:
  - defn (alpha-approximation) -> OL-ONLY
  - lem[transrecursionfun] (Bounded Recursion) -> OL-ONLY (stepping stone)
  - thm[transrecursionschema] (General Recursion) -> DEF-SET007 / THM-SET002
  - thm[simplerecursionschema] (Simple Recursion) -> OL-ONLY (variant of DEF-SET007)
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: sth/ordinals/ (all)
- **OL Cross-refs**: olref[ordinals][opps]{simpletransrecursion}, olref[ordinals][basic]{buraliforti}, olref[valpha]{defValphas}
- **Notes**: Proves the Transfinite Recursion Theorem(s) (DEF-SET007). Uses Transfinite Induction + Replacement. Vindicates the definition of V_alpha. Key technical section.

---

### sth/spine/Valphabasic -- Basic Properties of Stages
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/stagesbasics.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET001, DEF-SET004, DEF-SET005
- **OL Formal Items**:
  - defn (potent set) -> OL-ONLY
  - lem[Valphabasicprops] (V_alpha transitive, potent, cumulative) -> OL-ONLY
  - lem[Valphanotref] (V_alpha not in V_alpha) -> OL-ONLY
  - cor (alpha in beta iff V_alpha in V_beta) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/spine/valpha, sth/spine/recursion
- **OL Cross-refs**: (internal)
- **Notes**: Technical properties of the V_alpha hierarchy: transitivity, potency, cumulativity. Establishes that V_alpha faithfully reflects ordinal ordering.

---

### sth/spine/foundation -- Foundation
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/foundation.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: AX-Foundation (presented as axiom, not in taxonomy)
- **References**: DEF-SET001
- **OL Formal Items**:
  - defish[Regularity] -> OL-ONLY (formulation using V_alpha)
  - axiom[Foundation] -> OL-ONLY (equivalent to Regularity)
  - defn (transitive closure trcl(A)) -> OL-ONLY
  - prop[subsetoftrcl] -> OL-ONLY
  - lem[lem:TransitiveWellFounded] -> OL-ONLY
  - thm[zfentailsregularity] (Foundation implies Regularity) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/spine/Valphabasic
- **OL Cross-refs**: olref[z][story]{sec}, olref[ordinals][opps]{defsupstrict}, olref[spine][rank]{zfminusregularityfoundation}
- **Notes**: Introduces the Foundation axiom (equivalent to Regularity over ZF^-). Not in the main taxonomy as a separate item since it is a structural/well-foundedness axiom auxiliary to ZFC. It ensures every set appears in the V_alpha hierarchy.

---

### sth/spine/zf -- Z and ZF: A Milestone
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/zf.tex`
- **Domain**: SET
- **Introduces**: (none new -- defines theories Z and ZF)
- **References**: AX-SET001 through AX-SET008 (all except Choice)
- **OL Formal Items**:
  - defn (Z = Z^- + Foundation) -> OL-ONLY
  - defn (ZF = ZF^- + Foundation = Z + Replacement) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/spine/foundation
- **OL Cross-refs**: olref[recursion]{sec}
- **Notes**: Milestone defining Z and ZF. Explains why Foundation (rather than Regularity) is taken as basic: Regularity requires V_alpha, which requires Replacement.

---

### sth/spine/rank -- Rank
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/spine/rank.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- OL-ONLY: DEF-rank)
- **References**: DEF-SET001, DEF-SET006
- **OL Formal Items**:
  - defn[defnsetrank] (rank of a set) -> OL-ONLY
  - prop[ranksexist] -> OL-ONLY
  - prop[valphalowerrank] -> OL-ONLY
  - prop[rankmemberslower] -> OL-ONLY (B in A implies rank(B) < rank(A))
  - thm (epsilon-Induction Scheme) -> OL-ONLY (induction on all sets)
  - prop[ranksupstrict] -> OL-ONLY
  - cor[ordsetrankalpha] (rank(alpha) = alpha for ordinals) -> OL-ONLY
  - prop[zfminusregularityfoundation] (Regularity implies Foundation) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/spine/foundation, sth/spine/Valphabasic
- **OL Cross-refs**: olref[foundation]{sec}, olref[ordinals][basic]{ordinductionschema}, olref[Valphabasic]{Valphabasicprops}
- **Notes**: Defines rank and proves epsilon-induction. The rank of an ordinal equals itself. Completes the Foundation-Regularity equivalence.

---

## Chapter 5: replacement/ -- Replacement (7 sections)

### sth/replacement/intro -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/introduction.tex`
- **Domain**: SET
- **Introduces**: (none)
- **References**: AX-SET007 (Replacement)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/spine/ (all)
- **OL Cross-refs**: olref[sth][card-arithmetic][fix]{sec}
- **Notes**: Brief introduction framing the question of justifying Replacement.

---

### sth/replacement/strength -- The Strength of Replacement
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/strength.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement), DEF-SET001
- **OL Formal Items**:
  - defn[formularelativization] (relativization of formulas to a set M) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/replacement/intro
- **OL Cross-refs**: olref[ordinals][replacement]{sec}, olref[ordinals][idea]{sec}, olref[ordinals][ordtype]{thmOrdinalRepresentation}, olref[spine][rank]{ordsetrankalpha}
- **Notes**: Shows Z cannot prove existence of omega+omega (V_{omega+omega} is a model of Z). Hence Replacement is genuinely stronger. Introduces formula relativization.

---

### sth/replacement/extrinsic -- Extrinsic Considerations about Replacement
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/extrinsic.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/replacement/strength
- **OL Cross-refs**: (none)
- **Notes**: Philosophical discussion of extrinsic justification for Replacement (Boolos). Discusses Level Theory (LT) and Z_r as alternatives that achieve many of the same desirable consequences.

---

### sth/replacement/limofsize -- Limitation-of-size
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/limofsize.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement), PRIM-SET003 (proper class -- implicit)
- **OL Formal Items**:
  - (informal principle: LimOfSize) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/replacement/extrinsic
- **OL Cross-refs**: olref[sth][story][rus]{sec}
- **Notes**: Discusses limitation-of-size as an intrinsic justification for Replacement. Criticizes the approach as not well-motivated by the cumulative-iterative conception.

---

### sth/replacement/absinf -- Replacement and "Absolute Infinity"
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/absinf.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement)
- **OL Formal Items**:
  - (informal principles: StagesInex, StagesCofin) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/replacement/limofsize
- **OL Cross-refs**: olref[ordinals][idea]{sec}, olref[ordinals][ordtype]{thmOrdinalRepresentation}, olref[sth][replacement][finiteaxiomatizability]{sec}
- **Notes**: Discusses Shoenfield's cofinality-based justification for Replacement. The idea: the hierarchy is not cofinal with any set. More promising intrinsic justification than limitation-of-size.

---

### sth/replacement/ref -- Replacement and Reflection
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/ref.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: Reflection Schema
- **References**: AX-SET007 (Replacement)
- **OL Formal Items**:
  - thm[reflectionschema] (Reflection Schema) -> OL-ONLY (equivalent to Replacement over Z)
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/replacement/absinf
- **OL Cross-refs**: olref[sth][replacement][strength]{formularelativization}, olref[sth][replacement][refproofs]{sec}
- **Notes**: States the Reflection Schema (equivalent to Replacement over Z, per Montague-Levy). Philosophical discussion of how StagesInex justifies Reflection.

---

### sth/replacement/refproofs -- Appendix: Results surrounding Replacement
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/refproofs.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement), AX-SET006 (Separation)
- **OL Formal Items**:
  - lem[lemreflection] -> OL-ONLY
  - proof (of Reflection Schema) -> OL-ONLY
  - defish[Weak-Reflection] -> OL-ONLY
  - lem[lem:reflect] (reflect two formulas at once) -> OL-ONLY
  - thm[thm:replacement] (Weak-Reflection implies Replacement over Z) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/replacement/ref
- **OL Cross-refs**: olref[sth][replacement][ref]{reflectionschema}, olref[sth][replacement][strength]{formularelativization}
- **Notes**: Most advanced mathematics in the textbook. Proves Reflection in ZF, and proves Replacement from Weak-Reflection + Z. Establishes the Montague-Levy equivalence.

---

### sth/replacement/finiteaxiomatizability -- Appendix: Finite axiomatizability
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/replacement/finiteaxiomatizability.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET007 (Replacement)
- **OL Formal Items**:
  - thm[zfnotfinitely] (ZF is not finitely axiomatizable -- Montague) -> OL-ONLY
  - prop[finiteextensionofZ] (no finite extension of Z proves ZF, unless inconsistent) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/replacement/refproofs
- **OL Cross-refs**: olref[sth][replacement][absinf]{sec}, olref[ordinals][ordtype]{thmOrdinalRepresentation}
- **Notes**: Proves ZF is not finitely axiomatizable (Montague's theorem). Consequence: Replacement is strictly stronger than the Ordinal Representation Theorem.

---

## Chapter 6: ord-arithmetic/ -- Ordinal Arithmetic (5 sections)

### sth/ord-arithmetic/intro -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ord-arithmetic/introduction.tex`
- **Domain**: SET
- **Introduces**: (none)
- **References**: DEF-SET001
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/ordinals/ (all), sth/spine/ (all)
- **OL Cross-refs**: olref[ordinals][]{chap}, olref[spine][]{chap}, olref[ordinals][idea]{sec}
- **Notes**: Brief motivational introduction to ordinal arithmetic.

---

### sth/ord-arithmetic/add -- Ordinal Addition
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ord-arithmetic/addition.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-ordinal-addition
- **References**: DEF-SET001, DEF-SET004, DEF-SET005
- **OL Formal Items**:
  - defn[defdissum] (disjoint sum) -> OL-ONLY
  - defn (reverse lexicographic ordering) -> OL-ONLY
  - defn[defordplus] (ordinal addition) -> OL-ONLY
  - lem[ordsumlessiswo] -> OL-ONLY
  - lem[ordadditionrecursion] (recursion equations for addition) -> OL-ONLY
  - lem[ordinaladditionisnice] (monotonicity, cancellation, associativity) -> OL-ONLY
  - prop[ordsumnotcommute] (addition not commutative) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ordinals/ordtype
- **OL Cross-refs**: olref[ordinals][ordtype]{thmOrdinalRepresentation}, olref[ordinals][basic]{ordinalsaresubsets}
- **Notes**: Defines ordinal addition both synthetically and recursively. Key observation: ordinal addition is not commutative (1+omega = omega < omega+1).

---

### sth/ord-arithmetic/using-addition -- Using Ordinal Addition
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ord-arithmetic/using-addition.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET001, DEF-SET004, DEF-SET005
- **OL Formal Items**:
  - lem[rankcomputation] (rank computations for powerset, pairs, union, etc.) -> OL-ONLY
  - lem[ordinfinitycharacter] (5 equivalent characterizations of infinite ordinals) -> OL-ONLY
- **Role**: APPLY
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ord-arithmetic/add
- **OL Cross-refs**: olref[spine][rank]{defnsetrank}, olref[spine][rank]{ranksupstrict}, olref[z][infinity-again]{naturalnumbersarentinfinite}
- **Notes**: Uses ordinal addition to compute ranks of various set constructions. Proves equivalence of five characterizations of infinite ordinals (not in omega, omega <= alpha, 1+alpha=alpha, alpha equinumerous alpha+1, Dedekind infinite).

---

### sth/ord-arithmetic/mult -- Ordinal Multiplication
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ord-arithmetic/multiplication.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-ordinal-multiplication
- **References**: DEF-SET001, DEF-SET004, DEF-SET005
- **OL Formal Items**:
  - defn (ordinal multiplication via reverse lex on Cartesian product) -> OL-ONLY
  - lem[ordtimeslessiswo] -> OL-ONLY
  - lem[ordtimesrecursion] (recursion equations for multiplication) -> OL-ONLY
  - lem[ordinalmultiplicationisnice] (properties) -> OL-ONLY
  - prop (multiplication not commutative: 2*omega = omega < omega*2) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ord-arithmetic/add
- **OL Cross-refs**: olref[add]{ordsumnotcommute}
- **Notes**: Defines ordinal multiplication. Not commutative.

---

### sth/ord-arithmetic/expo -- Ordinal Exponentiation
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/ord-arithmetic/exponentiation.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-ordinal-exponentiation
- **References**: DEF-SET001, DEF-SET007 (Transfinite Recursion)
- **OL Formal Items**:
  - defn[ordexporecursion] (ordinal exponentiation by transfinite recursion) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ord-arithmetic/mult
- **OL Cross-refs**: (none external)
- **Notes**: Defines ordinal exponentiation purely by transfinite recursion (no nice synthetic definition). Not commutative: 2^omega = omega, but omega^2 = omega*omega.

---

## Chapter 7: cardinals/ -- Cardinals (5 sections)

### sth/cardinals/cp -- Cantor's Principle
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/cardinals/cp.tex`
- **Domain**: SET
- **Introduces**: DEF-SET008 (Cardinal Number -- motivation)
- **References**: DEF-SET001
- **OL Formal Items**:
  - (Cantor's Principle stated informally) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/ordinals/ordtype
- **OL Cross-refs**: olref[ordinals][vn]{sec}, olref[ordinals][ordtype]{ordtypesworklikeyouwant}, olref[sfr][siz][equ]{sec}, olref[hp]{sec}
- **Notes**: Motivates the notion of cardinal. Cantor's Principle: |A| = |B| iff A equinumerous B. Prepares for the formal definition.

---

### sth/cardinals/cardsasords -- Cardinals as Ordinals
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/cardinals/cardsasords.tex`
- **Domain**: SET
- **Introduces**: DEF-SET008, AX-SET009 (Well-Ordering)
- **References**: DEF-SET001, AX-SET007 (Replacement)
- **OL Formal Items**:
  - defn[defcardinalasordinal] (cardinal = least ordinal equinumerous to A) -> DEF-SET008
  - axiom[Well-Ordering] -> AX-SET009 (Well-Ordering Theorem taken as axiom)
  - lem[lem:CardinalsExist] (cardinals exist, are unique, idempotent) -> OL-ONLY
  - lem[lem:CardinalsBehaveRight] (Cantor's Principle holds) -> OL-ONLY
  - proof (re-proof of Schroder-Bernstein) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/cardinals/cp
- **OL Cross-refs**: olref[ordinals][ordtype]{thmOrdinalRepresentation}, olref[choice][]{chap}
- **Notes**: Defines cardinals as specific ordinals (DEF-SET008). Introduces the Well-Ordering axiom (AX-SET009) to guarantee every set has a cardinality. Proves Cantor's Principle formally.

---

### sth/cardinals/zfc -- ZFC: A Milestone
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/cardinals/milestone.tex`
- **Domain**: SET
- **Introduces**: (none new -- defines theory ZFC)
- **References**: AX-SET001 through AX-SET009 (all ZFC axioms)
- **OL Formal Items**:
  - defn (ZFC = ZF + Well-Ordering) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/cardinals/cardsasords
- **OL Cross-refs**: olref[choice][woproblem]{thmwochoice}
- **Notes**: Final milestone: ZFC = ZF + Well-Ordering = ZF + Choice. Notes the equivalence of Well-Ordering and Choice (proved later).

---

### sth/cardinals/classing -- Finite, Enumerable, Nonenumerable
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/cardinals/classing.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- but defines finite/infinite cardinals)
- **References**: DEF-SET008, AX-SET009, THM-SET002 (Cantor's Theorem, referenced from sfr)
- **OL Formal Items**:
  - prop[finitecardisoequal] -> OL-ONLY
  - cor[naturalsarecardinals] -> OL-ONLY
  - thm[generalinfinitycharacter] (3 equiv. characterizations of infinite sets) -> OL-ONLY
  - defn[defnfinite] (finite/infinite sets) -> OL-ONLY
  - cor[omegaisacardinal] (omega is least infinite cardinal) -> OL-ONLY
  - cor (infinite cardinal = limit ordinal) -> OL-ONLY
  - prop[unioncardinalscardinal] -> OL-ONLY
  - thm[lem:NoLargestCardinal] (no largest cardinal -- uses Cantor's Theorem) -> THM-SET002 (reference)
  - thm (no set of all cardinals) -> OL-ONLY (analogue of Burali-Forti for cardinals)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/cardinals/cardsasords
- **OL Cross-refs**: olref[ord-arithmetic][using-addition]{ordinfinitycharacter}, olref[sfr][siz][car]{thm:cantor}, olref[sfr][siz][enm-alt]{defn:enumerable}, olref[z][infinity-again]{naturalnumbersarentinfinite}, olref[choice][]{chap}
- **Notes**: Classifies cardinals as finite/enumerable/nonenumerable. Uses Cantor's Theorem (THM-SET002, defined in sfr/) to show no largest cardinal. The set of all cardinals doesn't exist (parallel to Burali-Forti).

---

### sth/cardinals/hp -- Appendix: Hume's Principle
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/cardinals/hp.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET008
- **OL Formal Items**:
  - (Hume's Principle -- discussed informally) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: sth/cardinals/cp
- **OL Cross-refs**: olref[cp]{sec}, olref[story][blv]{sec}, olref[story][predicative]{sec}
- **Notes**: Philosophical appendix comparing Cantor's Principle with Hume's Principle. Discusses neo-Fregean logicism. Relates to Basic Law V. No formal set-theoretic content.

---

## Chapter 8: card-arithmetic/ -- Cardinal Arithmetic (5 sections)

### sth/card-arithmetic/opps -- Defining the Basic Operations
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/card-arithmetic/opps.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: DEF-cardinal-arithmetic (addition, multiplication, exponentiation)
- **References**: DEF-SET008, THM-SET002 (Cantor's Theorem)
- **OL Formal Items**:
  - defn (cardinal addition, multiplication, exponentiation) -> OL-ONLY
  - prop[cardplustimescommute] (cardinal +,* commutative and associative) -> OL-ONLY
  - lem[lem:SizePowerset2Exp] (|P(A)| = 2^|A|) -> OL-ONLY
  - cor[cantorcor] (a < 2^a for any cardinal) -> THM-SET002 (reference; cardinal form of Cantor's Theorem)
  - thm[continuumis2aleph0] (|R| = 2^omega) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/cardinals/ (all)
- **OL Cross-refs**: olref[ord-arithmetic][add]{defdissum}, olref[sfr][siz][car]{thm:cantor}, olref[z][infinity-again]{defnomega}, olref[sfr][siz][red-alt]{sec}
- **Notes**: Defines cardinal arithmetic. The result |P(A)| = 2^|A| connects cardinal exponentiation to powersets. The cardinal Cantor's Theorem (a < 2^a) is the cardinal restatement of THM-SET002. Proves |R| = 2^omega.

---

### sth/card-arithmetic/simp -- Simplifying Addition and Multiplication
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/card-arithmetic/simp.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET008
- **OL Formal Items**:
  - defn (canonical ordering on pairs of ordinals) -> OL-ONLY
  - prop[simplecardproduct] -> OL-ONLY
  - lem[alphatimesalpha] (alpha equinumerous alpha x alpha for infinite alpha) -> OL-ONLY (key lemma)
  - thm[cardplustimesmax] (a * b = a + b = max(a,b) for infinite cardinals) -> OL-ONLY
  - prop[kappaunionkappasize] (kappa-union of kappa-size sets has size kappa) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/card-arithmetic/opps
- **OL Cross-refs**: olref[sfr][siz][zigzag]{natsquaredenumerable}, olref[ord-arithmetic][using-addition]{ordinfinitycharacter}
- **Notes**: Major simplification: for infinite cardinals, addition and multiplication collapse to max. The canonical ordering and the lemma that alpha x alpha = alpha (for infinite alpha) are the key technical tools.

---

### sth/card-arithmetic/expotough -- Some Simplification with Cardinal Exponentiation
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/card-arithmetic/expotough.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET008
- **OL Formal Items**:
  - prop[simplecardexpo] (exponent laws) -> OL-ONLY
  - prop[cardexpo2reduct] (a^b = 2^b when 2 <= a <= b, b infinite) -> OL-ONLY
  - prop (a^n = a for infinite a, finite n) -> OL-ONLY
  - prop (a^b = 2^b when 2 <= b < a <= 2^b, b infinite) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/card-arithmetic/simp
- **OL Cross-refs**: olref[opps]{lem:SizePowerset2Exp}, olref[simp]{cardplustimesmax}
- **Notes**: Partial simplification of cardinal exponentiation. Cannot fully simplify because of CH-related issues.

---

### sth/card-arithmetic/ch -- The Continuum Hypothesis
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/card-arithmetic/ch.tex`
- **Domain**: SET
- **Introduces**: DEF-SET013 (Aleph Numbers), DEF-SET015 (Continuum Hypothesis)
- **References**: DEF-SET008, THM-SET002
- **OL Formal Items**:
  - defn (aleph numbers, beth numbers) -> DEF-SET013 [Phase 2.5 correction: was DEF-SET009]
  - defish[GCH] (Generalized Continuum Hypothesis) -> DEF-SET015 [Phase 2.5 correction: was DEF-SET010]
  - defish[CH] (Continuum Hypothesis) -> DEF-SET015
  - prop (every infinite cardinal is an aleph) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: sth/card-arithmetic/expotough
- **OL Cross-refs**: olref[cardinals][classing]{lem:NoLargestCardinal}, olref[cardinals][classing]{unioncardinalscardinal}, olref[opps]{continuumis2aleph0}
- **Notes**: Defines aleph numbers (DEF-SET013) and the Continuum Hypothesis (DEF-SET015). States independence of CH. [Phase 2.5 correction: DEF-SET009 (Well-Ordering) and DEF-SET010 (Zorn's Lemma) are defined in sth/choice/woproblem, not here.]

---

### sth/card-arithmetic/fix -- Aleph-Fixed Points
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/card-arithmetic/fix.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: DEF-SET009, AX-SET007 (Replacement)
- **OL Formal Items**:
  - prop[alephfixed] (existence of aleph-fixed-point) -> OL-ONLY
  - prop[bethfixed] (existence of beth-fixed-point) -> OL-ONLY
  - prop[stagesize] (|V_{omega+alpha}| = beth_alpha) -> OL-ONLY
  - cor (exists kappa with |V_kappa| = kappa) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/card-arithmetic/ch
- **OL Cross-refs**: olref[spine][]{chap}, olref[cardinals][classing]{unioncardinalscardinal}, olref[replacement][extrinsic]{sec}
- **Notes**: Illustrates the "height" forced by Replacement: aleph-fixed-points and beth-fixed-points exist. Shows the hierarchy eventually becomes "as wide as it is tall." Includes Boolos's philosophical worry about the largeness of such cardinals.

---

## Chapter 9: choice/ -- Choice (7 sections)

### sth/choice/intro -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/introduction.tex`
- **Domain**: SET
- **Introduces**: (none)
- **References**: AX-SET009 (Well-Ordering)
- **OL Formal Items**: (none)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/cardinals/ (all), sth/card-arithmetic/ (all)
- **OL Cross-refs**: (none)
- **Notes**: Brief introduction to the Choice chapter.

---

### sth/choice/tarskiscott -- The Tarski-Scott Trick
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/tarskiscott.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy -- OL-ONLY: Tarski-Scott trick, TS-cardinals)
- **References**: DEF-SET008
- **OL Formal Items**:
  - defn[Tarski-Scott] (objects of least possible rank satisfying a formula) -> OL-ONLY
  - defn (TS-cardinality, TS-ordinality without Well-Ordering) -> OL-ONLY
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/choice/intro
- **OL Cross-refs**: olref[cardinals][cardsasords]{defcardinalasordinal}, olref[cardinals][cardsasords]{lem:CardinalsBehaveRight}, olref[card-arithmetic][opps]{lem:SizePowerset2Exp}, olref[spine][foundation]{zfentailsregularity}, olref[cardinals][hp]{sec}
- **Notes**: Shows how to define cardinals/ordinals without Choice, using the Tarski-Scott trick (least-rank representatives). This is an alternative to the standard definition that requires Well-Ordering.

---

### sth/choice/hartogs -- Comparability and Hartogs' Lemma
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/hartogs.tex`
- **Domain**: SET
- **Introduces**: OL-ONLY: Hartogs' Lemma
- **References**: AX-SET007 (Replacement), AX-SET006 (Separation), DEF-SET001
- **OL Formal Items**:
  - lem[HartogsLemma] (for any set A there is an ordinal not injectable into A) -> OL-ONLY
  - thm (Well-Ordering iff Comparability -- in ZF) -> OL-ONLY
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/choice/tarskiscott
- **OL Cross-refs**: olref[ord-arithmetic][using-addition]{rankcomputation}, olref[ordinals][ordtype]{thmOrdinalRepresentation}, olref[ordinals][basic]{corordtransitiveord}, olref[ordinals][iso]{wellordinitialsegment}, olref[ordinals][basic]{ordinalsaresubsets}, olref[card-arithmetic][simp]{cardplustimesmax}
- **Notes**: Proves Hartogs' Lemma (in ZF, no Choice needed). Then proves: Well-Ordering is equivalent to the comparability of all sets by size. Without Well-Ordering, some sets are incomparable in size.

---

### sth/choice/woproblem -- The Well-Ordering Problem
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/wellorderingproblem.tex`
- **Domain**: SET
- **Introduces**: AX-SET009 (Choice -- equivalent formulation), THM-SET001
- **References**: AX-SET009 (Well-Ordering), DEF-SET007 (Transfinite Recursion), AX-SET005 (Power Set)
- **OL Formal Items**:
  - defn (choice function, choice function for A) -> OL-ONLY
  - axiom[Choice] -> AX-SET009 (equivalent to Well-Ordering)
  - thm[thmwochoice] (Well-Ordering and Choice are equivalent in ZF) -> THM-SET001
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: sth/choice/hartogs
- **OL Cross-refs**: olref[hartogs]{HartogsLemma}
- **Notes**: Defines the Axiom of Choice and proves its equivalence with Well-Ordering (THM-SET001). The proof of Choice -> Well-Ordering uses transfinite recursion. AX-SET009 encompasses both Well-Ordering and Choice.

---

### sth/choice/countablechoice -- Countable Choice
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/countablechoice.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET009 (Choice)
- **OL Formal Items**:
  - lem (every finite set has a choice function -- in Z^-) -> OL-ONLY
  - defish[Countable Choice] -> OL-ONLY
  - thm (every set is finite or infinite -- in Z^- + Countable Choice) -> OL-ONLY (Dedekind's theorem)
  - thm (countable union of countable sets is countable -- in Z^- + Countable Choice) -> OL-ONLY
- **Role**: APPLY
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: sth/choice/woproblem
- **OL Cross-refs**: olref[z][pairs]{prop:pairsconsequences}, olref[cardinals][classing]{generalinfinitycharacter}, olref[card-arithmetic][simp]{kappaunionkappasize}
- **Notes**: Discusses Countable Choice as a weaker principle than full Choice. Shows it was historically used implicitly (by Dedekind, Cantor). Includes Russell's boots-and-socks example.

---

### sth/choice/justifications -- Intrinsic Considerations about Choice
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/justifications.tex`
- **Domain**: SET
- **Introduces**: THM-SET003 (Zorn's Lemma -- mentioned as equivalent)
- **References**: AX-SET009 (Choice)
- **OL Formal Items**:
  - thm[choiceset] (Choice iff every disjoint non-empty family has a choice set) -> OL-ONLY
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: sth/choice/countablechoice
- **OL Cross-refs**: olref[z][story]{sec}, olref[replacement][extrinsic]{sec}
- **Notes**: Intrinsic justification of Choice via StagesAcc: every possible collection of earlier-available sets is formed, so choice sets exist. The equivalence of Choice with choice sets is stated. THM-SET003 (Zorn's Lemma) is discussed as equivalent but not formally proved here; the text refers to Potter for details.

---

### sth/choice/banach -- The Banach-Tarski Paradox
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/banach.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET009 (Choice)
- **OL Formal Items**:
  - thm[Banach-Tarski Paradox] -> OL-ONLY (stated, not proved)
- **Role**: DISCUSS
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: sth/choice/justifications
- **OL Cross-refs**: olref[replacement][extrinsic]{sec}, olref[his][set][pathology]{sec}
- **Notes**: Discusses the Banach-Tarski Paradox as an allegedly undesirable consequence of Choice. Argues it is no more paradoxical than other results about infinite sets. Contains the famous anagram joke.

---

### sth/choice/vitali -- Appendix: Vitali's Paradox
- **File**: `/home/quode/projects/OpenLogic/content/set-theory/choice/vitali.tex`
- **Domain**: SET
- **Introduces**: (none in taxonomy)
- **References**: AX-SET009 (Choice)
- **OL Formal Items**:
  - thm[vitaliparadox] (Vitali's Paradox in ZFC) -> OL-ONLY
  - lem[rotationsgroupabelian] -> OL-ONLY
  - lem[disjointgroup] -> OL-ONLY
  - lem[vitalicover] -> OL-ONLY
  - lem[vitalinooverlap] -> OL-ONLY
  - lem[pseudobanachtarski] -> OL-ONLY
  - cor[Vitali] (Vitali's unmeasurable set) -> OL-ONLY
  - thm[Hausdorff's Paradox] -> OL-ONLY (stated)
- **Role**: PROVE
- **Compression Signal**: TANGENTIAL
- **Ped. Prerequisites**: sth/choice/banach
- **OL Cross-refs**: olref[banach]{sec}, olref[card-arithmetic][simp]{kappaunionkappasize}
- **Notes**: Detailed proof of Vitali's Paradox (2D analogue of Banach-Tarski). Uses Choice to select representatives from equivalence classes on the unit circle. Also discusses Hausdorff's Paradox. Shows the "pieces" must be unmeasurable.

---

## Batch 8: Model Theory (content/model-theory/) — 22 sections

## Chapter 1: Basics of Model Theory (`mod/bas`)

### mod/bas/red -- Reducts and Expansions
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/reducts-and-expansions.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- these are auxiliary structural notions)
- **References**: PRIM-SEM001 (structure), PRIM-SEM002 (language/signature), PRIM-SEM003 (domain), PRIM-SEM005 (satisfaction)
- **OL Formal Items**:
  - defn[defn:reduct] -> OL-ONLY: SUPPORT-DEF (reduct/expansion of structure)
  - prop[prop:reduct] -> OL-ONLY: stepping stone for DEF-SEM011, DEF-SEM012
  - defn (unnamed, Expan notation) -> OL-ONLY: SUPPORT-DEF (expansion notation M(R))
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/syn (language), fol/sem (structure, satisfaction)
- **OL Cross-refs**: olref[mod][bas][red]{prop:reduct}
- **Notes**: Reduct/expansion is a prerequisite for substructure and embedding definitions. Not a taxonomy primitive itself, but structurally necessary. The `Expan{M}{R}` notation is used heavily in interpolation/definability.

---

### mod/bas/sub -- Substructures
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/substructures.tex`
- **Domain**: SEM
- **Introduces**: DEF-SEM011 (Substructure)
- **References**: PRIM-SEM001 (structure), PRIM-SEM003 (domain), PRIM-SEM002 (language)
- **OL Formal Items**:
  - defn[defn:substructure] -> DEF-SEM011
  - rem[rem:substructure] -> OL-ONLY: pedagogical (relational substructure simplification)
- **Role**: DEFINE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: mod/bas/red (reducts and expansions)
- **OL Cross-refs**: Referenced by mod/lin/alg (abstract-logics.tex, relativization property)
- **Notes**: Short section. The definition is the defining occurrence of DEF-SEM011. The remark about relational languages without functions is used in the Lindstrom chapter. No embedding or elementary substructure yet (those come later or are absent).

---

### mod/bas/ove -- Overspill
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/overspill.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy)
- **References**: THM-SEM001 / CP-003 (Compactness Theorem)
- **OL Formal Items**:
  - thm[overspill] -> OL-ONLY: stepping stone (application of compactness)
  - prop[inf-not-fo] -> OL-ONLY: GAP-CANDIDATE (non-expressibility of finiteness in FOL -- this is a significant metatheoretic observation closely related to CP-013 / Lindstrom)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/com (compactness theorem)
- **OL Cross-refs**: None explicit beyond compactness
- **Notes**: The overspill theorem is a classic application of compactness. The proposition that finiteness is not first-order expressible is a notable result but not given its own taxonomy ID. Could be folded under metatheory of FOL expressiveness limits.

---

### mod/bas/iso -- Isomorphic Structures
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/isomorphism.tex`
- **Domain**: SEM
- **Introduces**: PRIM-SEM013 (Elementary Equivalence), DEF-SEM013 (Isomorphism of Structures), THM-SEM001 (Isomorphism Lemma)
- **References**: PRIM-SEM001 (structure), PRIM-SEM005 (satisfaction), PRIM-SEM002 (language)
- **OL Formal Items**:
  - defn[defn:elem-equiv] -> PRIM-SEM013
  - defn[defn:isomorphism] -> DEF-SEM013
  - thm[thm:isom] -> THM-SEM001 (Isomorphism Lemma: isomorphic structures are elementarily equivalent)
  - defn (automorphism) -> OL-ONLY: SUPPORT-DEF (automorphism)
- **Role**: DEFINE / PROVE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: mod/bas/red (reducts/expansions), fol/sem (satisfaction)
- **OL Cross-refs**: olref[mod][bas][iso]{thm:isom}, olref[mod][bas][iso]{defn:isomorphism} -- referenced heavily by partial-iso, theory-of-m, nonstandard-arithmetic
- **Notes**: This is a key section. Elementary equivalence (PRIM-SEM013) and isomorphism (DEF-SEM013) are both introduced here. The theorem that iso implies elem-equiv is fundamental. The converse failure is shown in mod/bas/thm. Note: DEF-SEM012 (Embedding) is NOT defined here -- OpenLogic does not have a separate embedding definition in model-theory; the closest is isomorphism. GAP: DEF-SEM012 (embedding as injective homomorphism) is missing from OL.

---

### mod/bas/thm -- The Theory of a Structure
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/theory-of-m.tex`
- **Domain**: SEM
- **Introduces**: PRIM-SEM012 (Theory of a Structure, Th(M))
- **References**: PRIM-SEM013 (elementary equivalence), DEF-SEM013 (isomorphism), PRIM-SEM005 (satisfaction), DEF-SEM005 (completeness of a theory)
- **OL Formal Items**:
  - defn (Theory of M) -> PRIM-SEM012
  - prop (Th(M) is complete) -> OL-ONLY: stepping stone for PRIM-SEM012
  - prop[prop:equiv] -> OL-ONLY: stepping stone (models of Th(M) are elementarily equivalent)
  - rem[remark:R] -> OL-ONLY: pedagogical (Lowenheim-Skolem counterexample to converse of iso->elem-equiv)
- **Role**: DEFINE / PROVE
- **Compression Signal**: CORE-DEF
- **Ped. Prerequisites**: mod/bas/iso (elementary equivalence, isomorphism)
- **OL Cross-refs**: olref[mod][bas][thm]{prop:equiv}, olref[mod][bas][thm]{remark:R} -- referenced by mod/bas/dlo
- **Notes**: Defining occurrence of PRIM-SEM012. The remark about R = (Real, <) and Lowenheim-Skolem is a classic pedagogical example showing isomorphism is strictly stronger than elementary equivalence.

---

### mod/bas/pis -- Partial Isomorphisms
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/partial-iso.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- partial isomorphism is not a separate taxonomy item)
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM013 (elementary equivalence), PRIM-SEM002 (language)
- **OL Formal Items**:
  - defn (partial isomorphism) -> OL-ONLY: SUPPORT-DEF (partial isomorphism)
  - defn[defn:partialisom] -> OL-ONLY: SUPPORT-DEF (partial isomorphism with back-and-forth)
  - thm[thm:p-isom1] -> OL-ONLY: CORE-THM (enumerable partially isomorphic structures are isomorphic)
  - thm[thm:p-isom2] -> OL-ONLY: CORE-THM (partial iso implies elem equiv for relational languages)
  - defn (quantifier rank) -> OL-ONLY: SUPPORT-DEF (quantifier rank, n-equivalence)
  - prop[prop:qr-finite] -> OL-ONLY: stepping stone for Lindstrom
  - defn (I_n relations) -> OL-ONLY: SUPPORT-DEF (Ehrenfeucht-Fraisse game relations)
  - defn (approx_n) -> OL-ONLY: SUPPORT-DEF
  - thm[thm:b-n-f] -> OL-ONLY: CORE-THM (connection between I_n and n-equivalence)
  - cor[cor:b-n-f] -> OL-ONLY: stepping stone for Lindstrom
- **Role**: DEFINE / PROVE
- **Compression Signal**: STEPPING-STONE (for Lindstrom's theorem)
- **Ped. Prerequisites**: mod/bas/iso (isomorphism, elementary equivalence), mod/bas/sub (substructure)
- **OL Cross-refs**: Referenced by mod/bas/dlo, mod/lin/lsp, mod/lin/prf
- **Notes**: Heavy section. The back-and-forth method and Ehrenfeucht-Fraisse games are developed here as the technical backbone for both the DLO categoricity result and Lindstrom's theorem. Quantifier rank and n-equivalence are model-theoretic tools not captured in the current taxonomy. GAP-CANDIDATE: Ehrenfeucht-Fraisse games could deserve a taxonomy entry.

---

### mod/bas/dlo -- Dense Linear Orders
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/dlo.tex`
- **Domain**: SEM
- **Introduces**: DEF-SEM006 (Categoricity -- demonstrated here for aleph-0 categoricity of DLO)
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM013 (elementary equivalence), PRIM-SEM012 (Theory of a Structure)
- **OL Formal Items**:
  - defn (dense linear ordering without endpoints) -> OL-ONLY: SUPPORT-DEF (DLO axioms)
  - thm[thm:cantorQ] -> DEF-SEM006 (Cantor's theorem: aleph-0 categoricity of DLO, the canonical example of categoricity)
  - rem (R elem-equiv Q) -> OL-ONLY: pedagogical
- **Role**: PROVE / APPLY
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: mod/bas/pis (partial isomorphisms, back-and-forth), mod/bas/thm (theory of a structure)
- **OL Cross-refs**: olref[mod][bas][dlo]{thm:cantorQ} -- referenced by mod/bas/nsa
- **Notes**: The DLO categoricity result is the defining example for DEF-SEM006. Note however that the word "categoricity" is not explicitly used in the text; it is demonstrated rather than formally defined. The concept of aleph-0 categoricity is implicit. GAP: An explicit definition of categoricity (DEF-SEM006) is absent -- it is shown by example rather than formally stated.

---

### mod/bas/nsa -- Non-standard Models of Arithmetic (COMMENTED OUT)
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/basics/nonstandard-arithmetic.tex`
- **Domain**: SEM
- **Introduces**: (none new -- overlaps with mod/mar content)
- **References**: PRIM-SEM012 (Th(N)), DEF-SEM013 (isomorphism), PRIM-SEM013 (elementary equivalence), THM-SEM001 / CP-003 (compactness), DEF-SEM006 (categoricity implicit)
- **OL Formal Items**:
  - defn (standard model, true arithmetic) -> OL-ONLY: SUPPORT-DEF (duplicated in mod/mar)
  - defn (standard/non-standard structure) -> OL-ONLY: SUPPORT-DEF
  - thm[thm:non-std] -> OL-ONLY: CORE-THM (existence of non-standard models via compactness)
  - Block analysis (items 1-13) -> OL-ONLY: pedagogical / CORE exposition of non-standard model structure
- **Role**: PROVE / DISCUSS
- **Compression Signal**: PEDAGOGICAL (commented out from chapter; content duplicated/superseded by mod/mar)
- **Ped. Prerequisites**: mod/bas/iso, mod/bas/thm, mod/bas/dlo, fol/com (compactness)
- **OL Cross-refs**: olref[mod][bas][iso]{thm:isom}, olref[mod][bas][dlo]{thm:cantorQ}
- **Notes**: This section is **commented out** in the chapter file (basics.tex line 24). Its content substantially overlaps with the models-of-arithmetic chapter. The detailed block analysis of non-standard models appears in both this file and mod/mar/mpa.

---

## Chapter 2: Models of Arithmetic (`mod/mar`)

### mod/mar/int -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/introduction.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy)
- **References**: PRIM-SEM012 (Th(N), true arithmetic), DEF-SEM013 (isomorphism), THM-SEM001/CP-003 (compactness, implicit), INC-related items (Godel incompleteness, implicit)
- **OL Formal Items**:
  - (no labeled environments -- narrative introduction)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/sem (structures), fol/com (compactness), inc (incompleteness, referenced informally)
- **OL Cross-refs**: None explicit
- **Notes**: Motivational introduction connecting non-standard models to the incompleteness phenomena. Discusses Con(PA) and its negation in the context of non-standard witnesses.

---

### mod/mar/stm -- Standard Models of Arithmetic
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/standard-models.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- refines isomorphism-based notion of "standard")
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM012 (Th(N))
- **OL Formal Items**:
  - defn (standard structure) -> OL-ONLY: SUPPORT-DEF (standard = isomorphic to N)
  - prop[prop:standard-domain] -> OL-ONLY: stepping stone
  - prop[prop:thq-standard] -> OL-ONLY: stepping stone (model of Q with only standard elements is standard)
  - prop[prop:thq-unique-iso] -> OL-ONLY: stepping stone (uniqueness of isomorphism to standard model)
- **Role**: DEFINE / PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: mod/bas/iso (isomorphism), fol/sem (structures, numerals)
- **OL Cross-refs**: olref[mod][mar][stm]{prop:standard-domain} -- referenced by mod/mar/nst
- **Notes**: Establishes the technical foundation for distinguishing standard vs non-standard models. The proofs rely on properties derivable in Q.

---

### mod/mar/nst -- Non-Standard Models
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/non-standard-models.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- applies compactness to produce non-standard models)
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM012 (Th(N) = TA), THM-SEM001/CP-003 (compactness)
- **OL Formal Items**:
  - defn (non-standard structure, non-standard numbers) -> OL-ONLY: SUPPORT-DEF
  - prop (non-standard element implies non-standard structure) -> OL-ONLY: stepping stone
  - prop (TA has enumerable non-standard model) -> OL-ONLY: CORE-THM (existence of non-standard models via compactness)
- **Role**: DEFINE / PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: mod/mar/stm (standard models), fol/com (compactness)
- **OL Cross-refs**: olref[mod][mar][stm]{prop:standard-domain}
- **Notes**: The existence proof for non-standard models of TA is a canonical application of compactness.

---

### mod/mar/mdq -- Models of Q
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/models-of-q.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy)
- **References**: PRIM-SEM012 (Th(N)), PRIM-SEM001 (structure), PRIM-SEM005 (satisfaction)
- **OL Formal Items**:
  - ex[ex:model-K-of-Q] -> OL-ONLY: pedagogical (explicit non-standard model K of Q)
  - ex[ex:model-L-of-Q] -> OL-ONLY: pedagogical (explicit non-standard model L of Q with non-commutative addition)
- **Role**: APPLY / DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: mod/mar/nst (non-standard models), inc/req (Q axioms)
- **OL Cross-refs**: olref[inc][req][min]{lem:less-zero}, olref[inc][req][min]{lem:less-nsucc}
- **Notes**: Purely pedagogical section constructing explicit models. Demonstrates that Q is weak enough to have very simple non-standard models (with single non-standard element whose successor is itself). Shows Q does not prove commutativity of addition. Important for intuition but no new definitions.

---

### mod/mar/mpa -- Models of PA
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/models-of-pa.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- detailed structural analysis of non-standard models of PA)
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM012 (Th(N)), DEF-SEM006 (categoricity, implicit -- non-standard blocks ordered like rationals)
- **OL Formal Items**:
  - prop (nsless is linear strict order) -> OL-ONLY: stepping stone
  - prop[prop:M-discrete] -> OL-ONLY: stepping stone (0 least, successor immediate, predecessor exists)
  - prop (standard less than nonstandard) -> OL-ONLY: stepping stone
  - prop (block of x) -> OL-ONLY: SUPPORT-DEF (block structure of non-standard models)
  - prop (block ordering respects nsless) -> OL-ONLY: stepping stone
  - cor (disjoint blocks) -> OL-ONLY: stepping stone
  - prop (nonstandard addition leaves block) -> OL-ONLY: stepping stone
  - prop (no least nonstandard block) -> OL-ONLY: stepping stone
  - prop (no largest block) -> OL-ONLY: stepping stone
  - prop[prop:blocks-dense] -> OL-ONLY: stepping stone (blocks are dense)
  - explain (blocks ordered like rationals) -> OL-ONLY: pedagogical (omega + Q*Z structure)
- **Role**: PROVE / DISCUSS
- **Compression Signal**: STEPPING-STONE (detailed structural analysis)
- **Ped. Prerequisites**: mod/mar/nst, mod/mar/mdq, mod/bas/dlo (Cantor's theorem for the block ordering)
- **OL Cross-refs**: olref[mod][mar][mpa]{prop:M-discrete}, olref[mod][mar][mpa]{prop:blocks-dense}
- **Notes**: Rich structural analysis showing that countable non-standard models of PA have order type omega + Q*Z (standard block followed by rationally-many Z-chains). Mentions Vaught's theorem (number of countable models of a complete theory cannot be 2) without proof. No new taxonomy items introduced but deeply applies existing concepts.

---

### mod/mar/cmp -- Computable Models of Arithmetic
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/models-of-arithmetic/computable-models.tex`
- **Domain**: SEM / COMP
- **Introduces**: DEF-SEM008 (Decidable Theory -- tangentially; Tennenbaum's theorem is stated)
- **References**: DEF-SEM013 (isomorphism), PRIM-SEM001 (structure), PRIM-COMP (computability concepts)
- **OL Formal Items**:
  - defn (computable structure) -> OL-ONLY: SUPPORT-DEF (computable model)
  - ex[ex:comp-model-q] -> OL-ONLY: pedagogical (computable non-standard model of Q)
  - thm (Tennenbaum's Theorem) -> OL-ONLY: CORE-THM (N is the only computable model of PA)
- **Role**: DEFINE / DISCUSS
- **Compression Signal**: CORE-THM (Tennenbaum's theorem statement)
- **Ped. Prerequisites**: mod/mar/mdq (models of Q), mod/mar/mpa (models of PA)
- **OL Cross-refs**: olref[mod][mar][mdq]{ex:model-K-of-Q}, olref[mod][mar][mdq]{ex:model-L-of-Q}
- **Notes**: Tennenbaum's theorem is stated without proof. The notion of "computable model" connects model theory to computability. DEF-SEM008 (decidable theory) is related but not identical to "computable model" -- Tennenbaum says no non-standard model of PA has computable operations, which is a stronger structural claim. GAP: DEF-SEM008 (decidable theory) is not formally defined in OL model-theory; it appears tangentially through Tennenbaum. An explicit definition of "decidable theory" is absent here.

---

## Chapter 3: The Interpolation Theorem (`mod/int`)

### mod/int/int -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/interpolation/introduction.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- informal introduction)
- **References**: CP-011 (Craig's Interpolation, previewed), CP-012 (Beth's Definability, previewed)
- **OL Formal Items**:
  - (no labeled environments -- narrative introduction)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/sem (entailment), fol/com (completeness)
- **OL Cross-refs**: None explicit
- **Notes**: Brief motivational section. States the interpolation theorem informally and previews Beth's definability theorem and Robinson's joint consistency theorem as applications.

---

### mod/int/sep -- Separation of Sentences
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/interpolation/separation.tex`
- **Domain**: SEM
- **Introduces**: (none from taxonomy -- technical machinery for interpolation)
- **References**: THM-SEM001/CP-003 (compactness, used in proofs)
- **OL Formal Items**:
  - defn (separation, inseparability) -> OL-ONLY: SUPPORT-DEF (separation of sentence sets)
  - lem[lem:sep1] -> OL-ONLY: stepping stone for CP-011 (inseparability preserved under constant expansion)
  - lem[lem:sep2] -> OL-ONLY: stepping stone for CP-011 (inseparability preserved under witnessing)
- **Role**: PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: fol/com (compactness), fol/sem (entailment)
- **OL Cross-refs**: Referenced by mod/int/prf
- **Notes**: Technical lemmas that form the machinery for the interpolation proof. The notion of "separation" is a reformulation of interpolation in dual form.

---

### mod/int/prf -- Craig's Interpolation Theorem
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/interpolation/interpolation-proof.tex`
- **Domain**: SEM
- **Introduces**: CP-011 (Craig's Interpolation Theorem)
- **References**: THM-SEM001/CP-003 (compactness), DEF-SEM013 (isomorphism, used in proof), CP-001 (completeness theorem, referenced)
- **OL Formal Items**:
  - thm[thm:interpol] -> CP-011
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: mod/int/sep (separation lemmas), fol/com (completeness theorem)
- **OL Cross-refs**: olref[mod][int][sep]{lem:sep1}, olref[mod][int][sep]{lem:sep2}, olref[fol][com][cth]{thm:completeness}
- **Notes**: Full proof of Craig's Interpolation Theorem via the inseparability/maximally consistent pair construction. The proof uses both compactness and completeness. This is the defining occurrence of CP-011.

---

### mod/int/def -- The Definability Theorem
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/interpolation/definability.tex`
- **Domain**: SEM
- **Introduces**: CP-012 (Beth's Definability Theorem)
- **References**: CP-011 (Craig's Interpolation, used in proof), THM-SEM001/CP-003 (compactness, used in proof)
- **OL Formal Items**:
  - defn (explicit definition of P) -> OL-ONLY: SUPPORT-DEF (explicit definability)
  - defn (implicit definition of P) -> OL-ONLY: SUPPORT-DEF (implicit definability)
  - thm (Beth Definability Theorem) -> CP-012
- **Role**: DEFINE / PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: mod/int/prf (Craig's interpolation), mod/bas/red (expansion notation)
- **OL Cross-refs**: None explicit beyond the use of Craig's theorem
- **Notes**: Full proof of Beth's Definability Theorem as a consequence of Craig's Interpolation Theorem. The notions of explicit and implicit definability are formally defined here. This is the defining occurrence of CP-012.

---

## Chapter 4: Lindstrom's Theorem (`mod/lin`)

### mod/lin/int -- Introduction
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/lindstrom/introduction.tex`
- **Domain**: SEM / META
- **Introduces**: (none from taxonomy -- motivation)
- **References**: THM-SEM001/CP-003 (compactness), CP-002 (Lowenheim-Skolem)
- **OL Formal Items**:
  - (no labeled environments -- narrative introduction)
- **Role**: DISCUSS
- **Compression Signal**: PEDAGOGICAL
- **Ped. Prerequisites**: fol/com (compactness, Lowenheim-Skolem)
- **OL Cross-refs**: olref[fol][com][com]{thm:compactness}, olref[fol][com][dls]{thm:downward-ls}
- **Notes**: Brief motivational paragraph. States the goal: characterize first-order logic as the maximal logic with compactness and downward Lowenheim-Skolem.

---

### mod/lin/alg -- Abstract Logics
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/lindstrom/abstract-logics.tex`
- **Domain**: SEM / META
- **Introduces**: (none from current taxonomy -- but introduces the framework for CP-013)
- **References**: PRIM-SEM001 (structure), PRIM-SEM005 (satisfaction), PRIM-SEM013 (elementary equivalence, generalized), DEF-SEM011 (substructure)
- **OL Formal Items**:
  - defn (abstract logic) -> OL-ONLY: SUPPORT-DEF for CP-013 (abstract logic as pair (L, models_L))
  - defn (Mod(L), elementary equivalence in L) -> OL-ONLY: SUPPORT-DEF
  - defn (normal abstract logic, 7 properties) -> OL-ONLY: SUPPORT-DEF for CP-013
  - defn (at least as expressive, equivalent logics) -> OL-ONLY: SUPPORT-DEF for CP-013
  - rem (first-order logic is normal) -> OL-ONLY: pedagogical
- **Role**: DEFINE
- **Compression Signal**: STEPPING-STONE (essential framework for Lindstrom's theorem)
- **Ped. Prerequisites**: mod/bas/sub (substructure), mod/bas/red (reducts/expansions), mod/bas/iso (isomorphism)
- **OL Cross-refs**: olref[bas][sub]{rem:substructure}
- **Notes**: Introduces the abstract framework of "normal abstract logics" with 7 closure properties (L-Monotonicity, Expansion, Isomorphism, Renaming, Boolean, Quantifier, Relativization). This is the definitional backdrop against which Lindstrom's theorem is stated. GAP-CANDIDATE: The concept of "abstract logic" could be a taxonomy item in its own right.

---

### mod/lin/lsp -- Compactness and Lowenheim-Skolem Properties
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/lindstrom/ls-property.tex`
- **Domain**: SEM / META
- **Introduces**: (none from taxonomy -- extends properties to abstract setting)
- **References**: THM-SEM001/CP-003 (compactness, generalized), CP-002 (Lowenheim-Skolem, generalized), PRIM-SEM013 (elementary equivalence), DEF-SEM013 (isomorphism)
- **OL Formal Items**:
  - defn (Compactness Property for abstract logics) -> OL-ONLY: SUPPORT-DEF for CP-013
  - defn (Downward Lowenheim-Skolem property for abstract logics) -> OL-ONLY: SUPPORT-DEF for CP-013
  - thm[thm:abstract-p-isom] -> OL-ONLY: CORE-THM (partially isomorphic structures are L-equivalent under LS property)
- **Role**: DEFINE / PROVE
- **Compression Signal**: STEPPING-STONE
- **Ped. Prerequisites**: mod/lin/alg (abstract logics), mod/bas/pis (partial isomorphisms)
- **OL Cross-refs**: olref[bas][pis]{defn:partialisom}, olref[bas][pis]{thm:p-isom2}, olref[bas][pis]{thm:p-isom1}
- **Notes**: The key theorem here generalizes the back-and-forth result to abstract logics: partial isomorphism implies L-equivalence if the logic has the LS property. The proof constructs an elaborate combined structure encoding partial isomorphisms. This is the technical heart of the Lindstrom proof.

---

### mod/lin/prf -- Lindstrom's Theorem
- **File**: `/home/quode/projects/OpenLogic/content/model-theory/lindstrom/lindstrom-proof.tex`
- **Domain**: SEM / META
- **Introduces**: CP-013 (Lindstrom's Theorem)
- **References**: THM-SEM001/CP-003 (compactness), CP-002 (Lowenheim-Skolem), PRIM-SEM013 (elementary equivalence, n-equivalence), DEF-SEM013 (isomorphism)
- **OL Formal Items**:
  - lem[lem:lindstrom] -> OL-ONLY: stepping stone (n-equivalence invariance implies first-order equivalence)
  - thm[thm:lindstrom] -> CP-013
- **Role**: PROVE
- **Compression Signal**: CORE-THM
- **Ped. Prerequisites**: mod/lin/lsp (abstract LS property, abstract partial isomorphism theorem), mod/bas/pis (quantifier rank, b-n-f theorem)
- **OL Cross-refs**: olref[bas][pis]{prop:qr-finite}, olref[bas][pis]{thm:b-n-f}, olref[lsp]{thm:abstract-p-isom}
- **Notes**: Full proof of Lindstrom's theorem. Uses compactness to obtain a non-standard element in an ordering that encodes the I_n relations, then derives a partial isomorphism contradicting the separation hypothesis. This is the defining occurrence of CP-013.

---

## Summary

### Sections Mapped: 22
(7 basics + 1 commented-out basics + 6 models-of-arithmetic + 4 interpolation + 4 lindstrom = 22)

### Active Sections (in compiled text): 21
(mod/bas/nsa is commented out)

### Taxonomy Items Introduced (Defining Occurrences)

| Taxonomy ID | Name | Section |
|---|---|---|
| **PRIM-SEM012** | Theory of a Structure (Th(M)) | mod/bas/thm |
| **PRIM-SEM013** | Elementary Equivalence | mod/bas/iso |
| **DEF-SEM006** | Categoricity (aleph-0, by example) | mod/bas/dlo |
| **DEF-SEM011** | Substructure | mod/bas/sub |
| **DEF-SEM013** | Isomorphism of Structures | mod/bas/iso |
| **CP-011** | Craig's Interpolation Theorem | mod/int/prf |
| **CP-012** | Beth's Definability Theorem | mod/int/def |
| **CP-013** | Lindstrom's Theorem | mod/lin/prf |

**Total introduced: 8**

### Taxonomy Items Referenced (Defined Elsewhere)

| Taxonomy ID | Name | Sections Using |
|---|---|---|
| PRIM-SEM001 | Structure | nearly all |
| PRIM-SEM002 | Language/Signature | nearly all |
| PRIM-SEM003 | Domain | nearly all |
| PRIM-SEM005 | Satisfaction | nearly all |
| DEF-SEM005 | Completeness of a theory | mod/bas/thm |
| THM-SEM001/CP-003 | Compactness | mod/bas/ove, mod/mar/nst, mod/int/sep, mod/int/prf, mod/int/def, mod/lin/prf |
| CP-001 | Completeness Theorem | mod/int/prf |
| CP-002 | Lowenheim-Skolem | mod/lin/int, mod/lin/lsp, mod/lin/prf |

### Taxonomy Items NOT Found (Gaps)

| Taxonomy ID | Name | Status |
|---|---|---|
| **PRIM-SEM014** | Elementary Substructure | **ABSENT** -- not defined anywhere in model-theory/. The concept of substructure is defined (DEF-SEM011) and elementary equivalence is defined (PRIM-SEM013), but they are never combined into "elementary substructure" (A is elem. substructure of B iff A is substructure of B and for all sentences phi, A |= phi iff B |= phi with elements from A). |
| **DEF-SEM003** | Semantic Consistency (has a model) | **ABSENT** -- not explicitly defined in model-theory/, though the concept is used implicitly throughout. Likely defined elsewhere (fol/sem or fol/com). |
| **DEF-SEM008** | Decidable Theory | **ABSENT** -- Tennenbaum's theorem (mod/mar/cmp) is related but concerns computable models, not decidable theories per se. No formal definition of "decidable theory" appears. |
| **DEF-SEM012** | Embedding | **ABSENT** -- no general definition of embedding (injective homomorphism) appears. Only isomorphism (bijective embedding) is defined. |
| **DEF-SEM014** | Diagram (atomic/elementary) | **ABSENT** -- the diagram method is not presented in OL's model-theory. |
| **DEF-SEM015** | Type (model-theoretic) | **ABSENT** -- types are not discussed. |
| **DEF-SEM016** | Omitting Types | **ABSENT** -- the Omitting Types theorem is not discussed. |

### Compression Signals Summary

| Signal | Count | Sections |
|---|---|---|
| CORE-DEF | 3 | mod/bas/sub, mod/bas/iso, mod/bas/thm |
| CORE-THM | 6 | mod/bas/dlo, mod/mar/nst, mod/mar/cmp, mod/int/prf, mod/int/def, mod/lin/prf |
| STEPPING-STONE | 8 | mod/bas/red, mod/bas/ove, mod/bas/pis, mod/mar/stm, mod/int/sep, mod/lin/alg, mod/lin/lsp, mod/mar/mpa |
| PEDAGOGICAL | 5 | mod/bas/nsa, mod/mar/int, mod/mar/mdq, mod/int/int, mod/lin/int |

### Key Observations

1. **Model-theory/ is incomplete** as noted in the editorial comment. It lacks several standard model-theoretic concepts: elementary substructures, embeddings, diagrams, types, and omitting types (PRIM-SEM014, DEF-SEM012, DEF-SEM014, DEF-SEM015, DEF-SEM016).

2. **DEF-SEM006 (Categoricity)** is demonstrated by example (DLO) but never formally defined as a concept. The word "categoricity" does not appear in the text.

3. **The chapter structure has significant overlap**: mod/bas/nsa (commented out) duplicates content from mod/mar/mpa. The models-of-arithmetic chapter re-derives the block structure of non-standard models with more pedagogical detail.

4. **The Lindstrom chapter** has a deep dependency chain: it requires the full back-and-forth / Ehrenfeucht-Fraisse machinery from mod/bas/pis, which is itself a substantial piece of infrastructure not captured in the current taxonomy.

5. **Cross-chapter dependencies**: The interpolation proof (mod/int/prf) depends on the completeness theorem from fol/com. The Lindstrom proof (mod/lin/prf) depends on compactness from fol/com and the partial isomorphism apparatus from mod/bas/pis.
