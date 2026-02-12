# CROSS-DOMAIN-MAP v0.1

This document maps how the 5+1 domains interconnect: ownership of every primitive and definition, the dependency graph, composition patterns (metatheorems at domain intersections), and variant compatibility across logic systems.

---

## 1. Primitive Ownership Table

Every PRIM and DEF across the taxonomy, with owner, consumers, and applicable boundary principle.

### BST (Set-Bootstrap, Level-0)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-BST001 | Set | BST | SYN, SEM, DED, CMP, SET | P5 | both |
| PRIM-BST002 | Membership ($\in$) | BST | SYN, SEM, DED, CMP, SET | P5 | both |
| PRIM-BST003 | Subset ($\subseteq$) | BST | SEM, SET | P5 | both |
| PRIM-BST004 | Empty Set ($\emptyset$) | BST | SEM, DED, SET | P5 | both |
| PRIM-BST005 | Union/Intersection | BST | SYN, SEM, DED | P5 | both |
| PRIM-BST006 | Ordered Pair | BST | SEM, DED, CMP | P5 | both |
| PRIM-BST007 | Cartesian Product | BST | SEM, DED, CMP | P5 | both |
| PRIM-BST008 | Relation | BST | SYN, SEM, CMP | P5 | both |
| PRIM-BST009 | Function | BST | SYN, SEM, DED, CMP | P5 | both |
| PRIM-BST010 | Finite Sequence | BST | SYN, DED, CMP | P5 | both |
| PRIM-BST011 | Infinite Sequence | BST | SEM, CMP | P5 | FOL |
| PRIM-BST012 | Natural Number ($\mathbb{N}$) | BST | SYN, SEM, DED, CMP, SET | P5 | both |
| PRIM-BST013 | Mathematical Induction | BST | SYN, SEM, DED, CMP | P5 | both |
| PRIM-BST014 | Inductive Definition | BST | SYN, SEM, DED, CMP | P5 | both |
| PRIM-BST015 | Power Set (naive) | BST | SEM, SET | P5 | both |
| PRIM-BST016 | Cardinality (naive) | BST | SEM, CMP, SET | P5 | FOL |
| DEF-BST001 | Injection | BST | SEM, CMP, SET | P5 | both |
| DEF-BST002 | Surjection | BST | SEM, CMP | P5 | both |
| DEF-BST003 | Bijection | BST | SEM, CMP, SET | P5 | both |
| DEF-BST004 | Equivalence Relation | BST | SEM, SYN | P5 | both |
| DEF-BST005 | Partial Order | BST | SET, SEM | P5 | both |

### SYN (Syntax)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-SYN001 | Symbol | SYN | SEM, DED, CMP | P1 | both |
| PRIM-SYN002 | Variable | SYN | SEM, DED, CMP | P1 | both |
| PRIM-SYN003 | Logical Connective | SYN | SEM, DED | P1 | both |
| PRIM-SYN004 | Quantifier | SYN | SEM, DED | P1 | FOL |
| PRIM-SYN005 | Constant Symbol | SYN | SEM | P1 | FOL |
| PRIM-SYN006 | Function Symbol | SYN | SEM | P1 | FOL |
| PRIM-SYN007 | Relation Symbol | SYN | SEM | P1 | FOL |
| PRIM-SYN008 | Arity | SYN | SEM | P1 | FOL |
| PRIM-SYN009 | Language (Signature) | SYN | SEM, DED, CMP, SET | P1 | FOL |
| PRIM-SYN010 | Term | SYN | SEM, DED | P1 | FOL |
| PRIM-SYN011 | Atomic Formula | SYN | SEM, DED | P1 | both |
| PRIM-SYN012 | Formula (wff) | SYN | SEM, DED, CMP | P1 | both |
| PRIM-SYN013 | Sentence | SYN | SEM, DED, CMP | P1 | FOL |
| PRIM-SYN014 | Free Occurrence | SYN | SEM, DED | P1 | FOL |
| PRIM-SYN015 | Bound Occurrence | SYN | SEM, DED | P1 | FOL |
| PRIM-SYN016 | Scope | SYN | SEM, DED | P1 | FOL |
| PRIM-SYN017 | Subformula | SYN | SEM, DED | P1 | both |
| PRIM-SYN018 | Equality Symbol ($=$) | SYN | SEM, DED, SET | P1 | FOL |
| DEF-SYN001 | Substitution | SYN | SEM, DED | P1 | FOL |
| DEF-SYN002 | Simultaneous Substitution | SYN | SEM, DED | P1 | FOL |
| DEF-SYN003 | Free Variables ($\text{FV}$) | SYN | SEM, DED | P1 | FOL |
| DEF-SYN004 | Alphabetic Variant | SYN | SEM, DED | P1 | FOL |
| DEF-SYN005 | Structural Induction | SYN | SEM, DED | P1 | both |
| DEF-SYN006 | Structural Recursion | SYN | SEM, CMP | P1 | both |
| DEF-SYN007 | Formula Complexity | SYN | SEM, DED | P1 | both |
| DEF-SYN008 | Subterm | SYN | SEM | P1 | FOL |

### SEM (Semantics)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-SEM001 | Structure ($\mathfrak{A}$) | SEM | DED, SET, CMP | P1 | FOL |
| PRIM-SEM002 | Domain ($\|\mathfrak{A}\|$) | SEM | DED, CMP | P1 | FOL |
| PRIM-SEM003 | Interpretation | SEM | DED | P1 | FOL |
| PRIM-SEM004 | Variable Assignment | SEM | DED | P1 | FOL |
| PRIM-SEM005 | $x$-Variant | SEM | DED | P1 | FOL |
| PRIM-SEM006 | Term Valuation | SEM | DED | P1 | FOL |
| PRIM-SEM007 | Satisfaction ($\vDash$) | SEM | DED, CMP | P1 | both |
| PRIM-SEM008 | Truth in Structure | SEM | DED, CMP | P1 | both |
| PRIM-SEM009 | Logical Validity ($\vDash \varphi$) | SEM | DED, CMP | P2 | both |
| PRIM-SEM010 | Logical Consequence ($\Gamma \vDash \varphi$) | SEM | DED | P2 | both |
| PRIM-SEM011 | Model ($\mathfrak{A} \vDash T$) | SEM | DED, SET, CMP | P1 | both |
| PRIM-SEM012 | Isomorphism ($\cong$) | SEM | SET, CMP | P1 | FOL |
| PRIM-SEM013 | Substructure | SEM | SET | P1 | FOL |
| PRIM-SEM014 | Homomorphism | SEM | SET | P1 | FOL |
| PRIM-SEM015 | Truth-Value Assignment (PL) | SEM | DED | P1 | PL |
| DEF-SEM001 | Tarski Satisfaction Defn. | SEM | DED, CMP | P1 | both |
| DEF-SEM002 | Satisfiable | SEM | DED | P2 | both |
| DEF-SEM003 | Finitely Satisfiable | SEM | DED | P2 | both |
| DEF-SEM004 | Semantic Consistency | SEM | DED | P2 | both |
| DEF-SEM005 | Semantic Completeness (theory) | SEM | DED, CMP | P2 | FOL |
| DEF-SEM006 | Theory of a Structure | SEM | DED, CMP | P1 | FOL |
| DEF-SEM007 | Definable Set | SEM | CMP, SET | P1 | FOL |
| DEF-SEM008 | Elementary Equivalence ($\equiv$) | SEM | CMP | P1 | FOL |
| DEF-SEM009 | Tautology (PL Validity) | SEM | DED | P2 | PL |
| DEF-SEM010 | PL Consequence | SEM | DED | P2 | PL |
| DEF-SEM011 | Elementary Substructure | SEM | SET | P1 | FOL |
| DEF-SEM012 | Diagram | SEM | DED | P1 | FOL |
| DEF-SEM013 | Type (Complete Type) | SEM | — | P1 | FOL |
| DEF-SEM014 | Categoricity | SEM | SET | P1 | FOL |
| DEF-SEM015 | Ultraproduct | SEM | SET | P1 | FOL |
| DEF-SEM016 | Embedding | SEM | SET | P1 | FOL |

### DED (Deduction)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-DED001 | Axiom Schema | DED | SEM, CMP | P2 | both |
| PRIM-DED002 | Non-Logical Axiom | DED | SEM, SET | P2 | FOL |
| PRIM-DED003 | Rule of Inference | DED | SEM, CMP | P2 | both |
| PRIM-DED004 | Proof System | DED | SEM, CMP | P2 | both |
| PRIM-DED005 | Derivation | DED | SEM, CMP | P2 | both |
| PRIM-DED006 | Provability ($\vdash$) | DED | SEM, CMP | P2 | both |
| PRIM-DED007 | Structural Rule | DED | — | P2 | both |
| PRIM-DED008 | Sequent | DED | — | P2 | both |
| PRIM-DED009 | Assumption Discharge | DED | — | P2 | both |
| PRIM-DED010 | Theorem | DED | SEM, CMP | P2 | both |
| DEF-DED001 | Syntactic Consistency | DED | SEM, CMP | P2 | both |
| DEF-DED002 | Maximal Consistent Set | DED | SEM | P2 | both |
| DEF-DED003 | Deductive Closure | DED | SEM | P2 | both |
| DEF-DED004 | Conservative Extension | DED | SET, CMP | P2 | FOL |
| DEF-DED005 | Hilbert-Style System | DED | SEM, CMP | P2 | both |
| DEF-DED006 | Natural Deduction | DED | SEM, CMP | P2 | both |
| DEF-DED007 | Sequent Calculus | DED | SEM | P2 | both |
| DEF-DED008 | Tableau System | DED | CMP | P2 | both |
| DEF-DED009 | Derived Rule | DED | — | P2 | both |
| DEF-DED010 | Admissible Rule | DED | — | P2 | both |

### CMP (Computation)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-CMP001 | Computable Function | CMP | SEM, DED, SET | P3 | both |
| PRIM-CMP002 | Primitive Recursive Function | CMP | DED, SET | P3 | FOL |
| PRIM-CMP003 | $\mu$-Recursion | CMP | DED | P3 | FOL |
| PRIM-CMP004 | Turing Machine | CMP | SEM, DED | P3 | FOL |
| PRIM-CMP005 | Church-Turing Thesis | CMP | SEM, DED | P3 | FOL |
| PRIM-CMP006 | Decidable Set | CMP | SEM, DED | P3 | FOL |
| PRIM-CMP007 | Semi-Decidable (c.e.) Set | CMP | DED | P3 | FOL |
| PRIM-CMP008 | Halting Problem | CMP | SEM, DED | P3 | FOL |
| PRIM-CMP009 | Many-One Reducibility | CMP | SEM | P3 | FOL |
| PRIM-CMP010 | Diagonalization | CMP | SEM, DED | P3 | FOL |
| PRIM-CMP011 | Godel Numbering | CMP | SYN, DED, SEM | P3 | FOL |
| PRIM-CMP012 | Universal Turing Machine | CMP | DED | P3 | FOL |
| DEF-CMP001 | Partial Function | CMP | DED, SEM | P3 | FOL |
| DEF-CMP002 | Total Function | CMP | SEM | P3 | FOL |
| DEF-CMP003 | Characteristic Function | CMP | DED | P3 | FOL |
| DEF-CMP004 | Enumeration | CMP | DED | P3 | FOL |
| DEF-CMP005 | Index (Program) | CMP | DED | P3 | FOL |
| DEF-CMP006 | Lambda-Definable Function | CMP | DED | P3 | FOL |
| DEF-CMP007 | Productive Set | CMP | — | P3 | FOL |
| DEF-CMP008 | Creative Set | CMP | — | P3 | FOL |
| DEF-CMP009 | Representability | CMP | DED, SEM | P3 | FOL |
| DEF-CMP010 | Recursive Enumerability | CMP | DED | P3 | FOL |

### SET (Set-Formal, Level-1)

| ID | Concept | Owner | Referenced By | Boundary | Fragment |
|----|---------|-------|---------------|----------|----------|
| PRIM-SET001 | Set (formal) | SET | SEM | P5 | FOL |
| PRIM-SET002 | Membership ($\in$, formal) | SET | SYN | P5 | FOL |
| PRIM-SET003 | Class (informal) | SET | — | P5 | FOL |
| DEF-SET001 | Ordinal (von Neumann) | SET | SEM | P5 | FOL |
| DEF-SET002 | Successor Ordinal | SET | — | P5 | FOL |
| DEF-SET003 | Limit Ordinal | SET | — | P5 | FOL |
| DEF-SET004 | $\omega$ | SET | SEM, CMP | P5 | FOL |
| DEF-SET005 | Transfinite Induction | SET | SEM | P5 | FOL |
| DEF-SET006 | Transfinite Recursion | SET | SEM | P5 | FOL |
| DEF-SET007 | Cardinal Number | SET | SEM | P5 | FOL |
| DEF-SET008 | Cardinality (formal) | SET | SEM | P5 | FOL |
| DEF-SET009 | Well-Ordering | SET | SEM | P5 | FOL |
| DEF-SET010 | Zorn's Lemma | SET | DED, SEM | P5 | FOL |
| DEF-SET011 | Cantor's Theorem (formal) | SET | SEM | P5 | FOL |

**Total: 134 items** (21 BST + 26 SYN + 31 SEM + 20 DED + 22 CMP + 14 SET)

---

## 2. Domain Dependency Graph

```
BST (Level-0 root, no prerequisites)
 +-- SYN (depends: BST)
 |    +-- SEM (depends: SYN, BST)
 |    +-- DED (depends: SYN, BST)
 +-- CMP (depends: BST)
 +-- SET (depends: SYN, SEM, DED, BST)
```

**Reading the graph**:
- BST is consumed by all 5 other domains (universal metalanguage infrastructure).
- SYN depends only on BST. It provides the formal language apparatus.
- SEM and DED both depend on SYN and BST. They are independent of each other — their connection is via composition patterns (CP-001, CP-002), not direct imports.
- CMP depends only on BST. Its connections to SYN/SEM/DED are via composition patterns (CP-005 through CP-008).
- SET depends on everything (it is a first-order theory analyzed using the full SYN+SEM+DED apparatus, built from BST metalanguage).

---

## 3. Composition Patterns

Major metatheorems that live at domain intersections. These are the "crown jewels" of mathematical logic — results that CANNOT be stated within a single domain.

### CP-001: **Soundness (of FOL)**

- **Domains**: DED $\times$ SEM
- **Statement**: If $\Gamma \vdash \varphi$ then $\Gamma \vDash \varphi$. Every provable formula is logically valid; every derivable consequence is a semantic consequence.
- **Natural language**: The proof system never proves anything false. If you can derive $\varphi$ from $\Gamma$, then $\varphi$ is true in every structure that makes $\Gamma$ true.
- **Key dependencies**:
  - DED: PRIM-DED006 (provability), PRIM-DED003 (rule of inference), PRIM-DED001 (axiom schema), AX-DED001 (MP), AX-DED002 (Gen), AX-DED003 (logical axiom schemas)
  - SEM: PRIM-SEM010 (logical consequence), PRIM-SEM007 (satisfaction), DEF-SEM001 (Tarski definition)
- **Proof sketch**: By induction on the length of the derivation. Base case: every logical axiom instance is valid (verified by truth-table/structure analysis for each schema). Inductive step: each rule of inference (MP, Gen) preserves truth — if premises are true in a structure, the conclusion is too. MP: if $\mathfrak{A} \vDash \varphi$ and $\mathfrak{A} \vDash \varphi \to \psi$ then $\mathfrak{A} \vDash \psi$ (by the Tarski clause for $\to$). Gen: if $\mathfrak{A} \vDash \varphi$ for arbitrary assignment and $x$ not free in $\Gamma$, then $\mathfrak{A} \vDash \forall x\, \varphi$.
- **Source**: SRC-GLB001 (Enderton Ch. 2, Soundness Theorem)
- **Variant compatibility**: Universal — holds for classical, intuitionistic, modal, many-valued, SOL (with appropriate proof systems and semantics matched).
- **Significance**: Guarantees the proof system is trustworthy. Without soundness, proofs would be meaningless symbol games.

### CP-002: **Completeness (Godel 1930)**

- **Domains**: SEM $\times$ DED $\times$ BST
- **Statement**: If $\Gamma \vDash \varphi$ then $\Gamma \vdash \varphi$. Every semantic consequence is provable. Equivalently: every consistent set of formulas has a model.
- **Natural language**: The proof system is powerful enough to derive everything that is semantically true. Nothing is "missed."
- **Key dependencies**:
  - SEM: PRIM-SEM010 (logical consequence), PRIM-SEM011 (model), DEF-SEM002 (satisfiable), DEF-SEM004 (semantic consistency)
  - DED: PRIM-DED006 (provability), DEF-DED001 (syntactic consistency), DEF-DED002 (maximal consistent set), THM-DED005 (Lindenbaum's lemma)
  - BST: PRIM-BST016 (cardinality — countable languages), PRIM-BST013 (induction — on Henkin construction steps)
- **Proof sketch**: Henkin construction. (1) Extend $\Gamma$ to a maximal consistent set $\Gamma^*$ (Lindenbaum, THM-DED005). (2) Add Henkin witnesses: for each $\exists x\, \varphi(x)$, add a new constant $c$ and the axiom $\exists x\, \varphi(x) \to \varphi(c)$. (3) Build the term model: domain = equivalence classes of closed terms under $\Gamma^*$-provable equality. (4) Show this model satisfies $\Gamma^*$ (hence $\Gamma$) by induction on formula complexity.
- **Source**: SRC-GLB001 (Enderton Ch. 2), Godel "Die Vollstandigkeit des Logikkalkuls" (1930)
- **Variant compatibility**: Classical FOL (full strength). Intuitionistic: holds w.r.t. Kripke semantics. Modal: via canonical models for many normal modal logics. SOL (full): FAILS — Godel's completeness theorem does not hold for full second-order semantics.
- **Significance**: Bridges syntax and semantics. Makes $\vdash$ and $\vDash$ coextensive, justifying the use of either proof-theoretic or model-theoretic methods.

### CP-003: **Compactness**

- **Domains**: SEM $\times$ BST
- **Statement**: A set of sentences $\Gamma$ is satisfiable iff every finite subset of $\Gamma$ is satisfiable.
- **Natural language**: If you cannot find a contradiction in any finite piece of a theory, the whole theory has a model.
- **Key dependencies**:
  - SEM: DEF-SEM002 (satisfiable), DEF-SEM003 (finitely satisfiable), PRIM-SEM011 (model)
  - BST: PRIM-BST001 (set), PRIM-BST003 (subset)
- **Proof sketch**: Two standard proofs. (1) Via completeness (CP-002): $\Gamma$ is satisfiable iff consistent (by CP-002). Consistency is a finitary notion (every derivation is finite), so $\Gamma$ is consistent iff every finite subset is consistent iff every finite subset is satisfiable (by CP-002 again). (2) Via ultraproducts: take models $\mathfrak{A}_F$ of each finite subset $F$; the ultraproduct over a suitable ultrafilter satisfies all of $\Gamma$ (by Los's theorem, THM-SEM003).
- **Source**: SRC-GLB001 (Enderton Ch. 2), SRC-SEM003 (Chang & Keisler Ch. 4)
- **Variant compatibility**: Classical FOL: yes. Intuitionistic: yes (for Kripke semantics). SOL (full): NO.
- **Significance**: Enables "finitary" reasoning about infinite theories. Key tool for constructing non-standard models and transfer principles.

### CP-004: **Lowenheim-Skolem**

- **Domains**: SEM $\times$ BST
- **Statement**: (Downward) If $\Gamma$ has a model, it has a countable model. (Upward) If $\Gamma$ has an infinite model of any cardinality, it has models of every cardinality $\geq |\mathcal{L}|$.
- **Natural language**: First-order logic cannot pin down the size of its models. If a theory has any infinite model, it has models of every infinite size.
- **Key dependencies**:
  - SEM: PRIM-SEM011 (model), PRIM-SEM001 (structure), DEF-SEM011 (elementary substructure, for downward), DEF-SEM003 (finitely satisfiable, for upward via compactness)
  - BST: PRIM-BST016 (cardinality), DEF-BST003 (bijection)
- **Proof sketch**: Downward: Tarski-Vaught test — select countable witnesses for each existential statement using a countable sequence of choices. Upward: add $\kappa$ new constants and sentences saying they are all distinct; apply compactness (CP-003) to get a model of the expanded theory.
- **Source**: SRC-SEM001 (Enderton Ch. 2), SRC-SEM002 (Marker Ch. 2)
- **Variant compatibility**: Classical FOL: yes. Intuitionistic: NO (fails). Modal: limited. SOL: NO.
- **Significance**: Reveals a fundamental limitation of first-order logic — it cannot characterize structures up to isomorphism (beyond finite ones). Motivates the study of infinitary logics and second-order logic.

### CP-005: **Godel's First Incompleteness Theorem**

- **Domains**: SYN $\times$ DED $\times$ CMP $\times$ BST
- **Statement**: Any consistent, computably axiomatizable theory $T$ that extends Robinson arithmetic $Q$ is incomplete: there exists a sentence $G$ such that $T \nvdash G$ and $T \nvdash \neg G$.
- **Natural language**: No consistent effective formal system that can do basic arithmetic can prove all true arithmetic statements. There are always "blind spots."
- **Key dependencies**:
  - SYN: PRIM-SYN012 (formula), PRIM-SYN013 (sentence), DEF-SYN001 (substitution)
  - DED: PRIM-DED006 (provability), DEF-DED001 (syntactic consistency)
  - CMP: PRIM-CMP011 (Godel numbering), PRIM-CMP010 (diagonalization), DEF-CMP009 (representability), PRIM-CMP006 (decidable set)
  - BST: PRIM-BST012 ($\mathbb{N}$), PRIM-BST009 (function)
- **Proof sketch**: (1) Godel numbering (PRIM-CMP011) encodes formulas as numbers. (2) The provability predicate $\text{Prov}_T(\ulcorner \varphi \urcorner)$ is representable in $T$ (because $T$ is c.e. and extends $Q$). (3) By the diagonal lemma (a self-referential construction using PRIM-CMP010), construct $G$ such that $T \vdash G \leftrightarrow \neg \text{Prov}_T(\ulcorner G \urcorner)$ — "$G$ says 'I am not provable in $T$.'" (4) If $T \vdash G$, then $T \vdash \text{Prov}_T(\ulcorner G \urcorner)$ (since $T$ can verify its own proofs), but also $T \vdash \neg \text{Prov}_T(\ulcorner G \urcorner)$ (from $G$), contradicting consistency. (5) If $T \vdash \neg G$, then $T \vdash \text{Prov}_T(\ulcorner G \urcorner)$, but $T \nvdash G$ (from $\neg G$ and consistency), so $T$ proves $\text{Prov}_T(\ulcorner G \urcorner)$ while $G$ is actually not provable — this contradicts $\Sigma_1$-soundness (or $\omega$-consistency).
- **Source**: SRC-GLB005 (Godel 1931)
- **Variant compatibility**: Applies to any sufficiently strong consistent theory — classical, intuitionistic (Heyting Arithmetic), or any system that can represent computable functions.
- **Significance**: The crown jewel. Sets an absolute limit on what formal systems can achieve. Demonstrates that mathematical truth transcends formal provability.

### CP-006: **Godel's Second Incompleteness Theorem**

- **Domains**: SYN $\times$ DED $\times$ CMP $\times$ BST
- **Statement**: If $T$ is a consistent, computably axiomatizable theory extending $Q$, then $T \nvdash \text{Con}(T)$, where $\text{Con}(T)$ is the arithmetic sentence expressing "$T$ is consistent."
- **Natural language**: No sufficiently strong consistent system can prove its own consistency.
- **Key dependencies**: Same as CP-005, plus the derivability conditions (Hilbert-Bernays-Lob): (D1) if $T \vdash \varphi$ then $T \vdash \text{Prov}_T(\ulcorner \varphi \urcorner)$; (D2) $T \vdash \text{Prov}_T(\ulcorner \varphi \to \psi \urcorner) \to (\text{Prov}_T(\ulcorner \varphi \urcorner) \to \text{Prov}_T(\ulcorner \psi \urcorner))$; (D3) $T \vdash \text{Prov}_T(\ulcorner \varphi \urcorner) \to \text{Prov}_T(\ulcorner \text{Prov}_T(\ulcorner \varphi \urcorner) \urcorner)$.
- **Proof sketch**: Formalize the proof of the First Incompleteness Theorem within $T$. $\text{Con}(T) \equiv \neg \text{Prov}_T(\ulcorner 0 = 1 \urcorner)$. The First Theorem shows $\text{Con}(T) \to \neg \text{Prov}_T(\ulcorner G \urcorner)$. By the properties of $G$: $G \leftrightarrow \neg \text{Prov}_T(\ulcorner G \urcorner)$. So $\text{Con}(T) \to G$. If $T \vdash \text{Con}(T)$, then $T \vdash G$, contradicting the First Theorem.
- **Source**: SRC-GLB005 (Godel 1931)
- **Variant compatibility**: Same as CP-005.
- **Significance**: Hilbert's program (to prove the consistency of mathematics within a finitary system) is impossible for any system as strong as arithmetic.

### CP-007: **Tarski's Undefinability of Truth**

- **Domains**: SYN $\times$ SEM $\times$ CMP
- **Statement**: For any sufficiently expressive language $\mathcal{L}$ and structure $\mathfrak{A}$ for $\mathcal{L}$, the set $\text{Th}(\mathfrak{A}) = \{\ulcorner \varphi \urcorner : \mathfrak{A} \vDash \varphi\}$ is not definable in $\mathfrak{A}$ by any $\mathcal{L}$-formula.
- **Natural language**: No structure can define its own truth predicate. The concept "true in $\mathfrak{A}$" cannot be expressed by a formula of the language that $\mathfrak{A}$ interprets.
- **Key dependencies**:
  - SYN: PRIM-SYN012 (formula), PRIM-SYN013 (sentence)
  - SEM: PRIM-SEM008 (truth in structure), DEF-SEM006 (theory of structure), DEF-SEM007 (definable set)
  - CMP: PRIM-CMP011 (Godel numbering), PRIM-CMP010 (diagonalization)
- **Proof sketch**: Suppose truth is definable by $\text{True}(x)$: $\mathfrak{A} \vDash \text{True}(\ulcorner \varphi \urcorner)$ iff $\mathfrak{A} \vDash \varphi$. By the diagonal lemma, construct $L$ with $\mathfrak{A} \vDash L \leftrightarrow \neg \text{True}(\ulcorner L \urcorner)$. Then $\mathfrak{A} \vDash L$ iff $\mathfrak{A} \vDash \neg \text{True}(\ulcorner L \urcorner)$ iff $\mathfrak{A} \nvDash L$. Contradiction.
- **Source**: SRC-GLB004 (Tarski 1935)
- **Variant compatibility**: Classical FOL. Applies to any structure that can encode its own syntax.
- **Significance**: Explains why the semantics of a formal language must be developed in a richer metalanguage (as this taxonomy does with BST).

### CP-008: **Church's Undecidability of Validity**

- **Domains**: SEM $\times$ CMP
- **Statement**: The set of logically valid sentences of FOL is not decidable (though it is c.e.).
- **Natural language**: There is no algorithm that, given any first-order sentence, correctly determines whether it is logically valid.
- **Key dependencies**:
  - SEM: PRIM-SEM009 (logical validity)
  - CMP: PRIM-CMP006 (decidable set), PRIM-CMP008 (halting problem), PRIM-CMP009 (many-one reducibility)
- **Proof sketch**: Reduce the halting problem to validity. Given a Turing machine $M$ and input $w$, effectively construct a sentence $\varphi_{M,w}$ that is valid iff $M$ halts on $w$. Since the halting problem is undecidable (THM-CMP002), validity is undecidable. Validity IS c.e.: enumerate all proofs (which exist by completeness, CP-002) and check each.
- **Source**: SRC-GLB006 (Church 1936)
- **Variant compatibility**: Classical FOL. PL validity IS decidable (truth tables). SOL validity is not even c.e.
- **Significance**: Shows that while individual proofs can be verified (decidable), finding proofs in general cannot be automated.

### CP-009: **Deduction Theorem**

- **Domains**: DED (internal)
- **Statement**: If $\Gamma \cup \{\varphi\} \vdash \psi$ (with appropriate side conditions), then $\Gamma \vdash \varphi \to \psi$.
- **Natural language**: A conditional proof is always available: if you can prove $\psi$ by assuming $\varphi$, you can prove $\varphi \to \psi$ outright.
- **Key dependencies**: PRIM-DED006 (provability), AX-DED001 (MP), AX-DED003 (axiom schemas A1, A2)
- **Proof sketch**: See THM-DED001 in DOMAIN-DEDUCTION.md.
- **Source**: SRC-DED001 (Enderton Ch. 2)
- **Variant compatibility**: Classical FOL, intuitionistic, modal (with modifications for necessitation). Fails for some substructural logics (without weakening).
- **Significance**: Makes conditional proofs systematic. Essential for practical proof construction in Hilbert systems.

### CP-010: **Cut Elimination (Gentzen's Hauptsatz)**

- **Domains**: DED (internal)
- **Statement**: Every sequent provable in sequent calculus is provable without using the cut rule.
- **Natural language**: "Shortcuts" via lemmas are never necessary — every proof can be "unfolded" into a direct proof.
- **Key dependencies**: DEF-DED007 (sequent calculus), PRIM-DED007 (structural rules)
- **Proof sketch**: See THM-DED003 in DOMAIN-DEDUCTION.md.
- **Source**: SRC-GLB009 (Gentzen 1935)
- **Variant compatibility**: Classical FOL, intuitionistic, modal, many-valued. Limited for SOL.
- **Significance**: Cut-free proofs have the subformula property — every formula appearing in the proof is a subformula of the conclusion or hypotheses. This makes proof search more tractable and enables consistency proofs.

### CP-011: **Craig's Interpolation Theorem**

- **Domains**: SEM $\times$ SYN
- **Statement**: If $\vDash \varphi \to \psi$ (or equivalently $\vdash \varphi \to \psi$), then there exists a sentence $\theta$ (the interpolant) such that: (i) $\vDash \varphi \to \theta$ and $\vDash \theta \to \psi$; (ii) every non-logical symbol in $\theta$ occurs in both $\varphi$ and $\psi$.
- **Natural language**: If $\varphi$ implies $\psi$, there is an "intermediate" statement $\theta$ that captures exactly the common content between them.
- **Key dependencies**:
  - SEM: PRIM-SEM009 (validity), PRIM-SEM010 (consequence)
  - SYN: PRIM-SYN009 (language), PRIM-SYN001 (symbol)
- **Proof sketch**: Standard proof via cut elimination in sequent calculus. In a cut-free proof of $\varphi \Rightarrow \psi$, the "midsequent" at the boundary of the $\varphi$-part and $\psi$-part of the proof tree provides the interpolant.
- **Source**: Craig, "Three uses of the Herbrand-Gentzen theorem," 1957
- **Variant compatibility**: Classical FOL: yes. Intuitionistic: yes. Modal: varies (fails for some normal modal logics).
- **Significance**: Reveals the "common content" between premises and conclusions. Applications in database theory, software verification.

### CP-012: **Beth's Definability Theorem**

- **Domains**: SEM $\times$ SYN
- **Statement**: If a relation symbol $R$ is implicitly definable by a theory $T$ (i.e., any two models of $T$ that agree on all other symbols agree on $R$), then $R$ is explicitly definable (there is an $\mathcal{L} \setminus \{R\}$-formula $\varphi(\bar{x})$ such that $T \vdash R(\bar{x}) \leftrightarrow \varphi(\bar{x})$).
- **Natural language**: If a theory forces a unique interpretation for a symbol, there must be an explicit definition of that symbol in terms of the others.
- **Key dependencies**:
  - SEM: PRIM-SEM011 (model), DEF-SEM007 (definable set)
  - SYN: PRIM-SYN007 (relation symbol), PRIM-SYN009 (language)
- **Proof sketch**: Via Craig's interpolation theorem (CP-011). If $R$ is implicitly definable, then $T(R) \land T(R') \vDash R(\bar{x}) \leftrightarrow R'(\bar{x})$ (where $R'$ is a copy of $R$). By interpolation, there exists $\varphi(\bar{x})$ in the common language (without $R$ or $R'$) such that $T \vDash R(\bar{x}) \leftrightarrow \varphi(\bar{x})$.
- **Source**: Beth, "On Padoa's method in the theory of definition," 1953
- **Variant compatibility**: Classical FOL. Intuitionistic: yes. Modal: varies.
- **Significance**: Connects semantic implicit definability with syntactic explicit definability.

### CP-013: **Lindstrom's Theorem**

- **Domains**: SEM $\times$ SYN $\times$ BST
- **Statement**: First-order logic is the strongest logic satisfying both the Compactness Theorem (CP-003) and the Downward Lowenheim-Skolem Theorem (CP-004).
- **Natural language**: FOL is "optimal" among logics: any logic that is more expressive than FOL must lose either compactness or downward Lowenheim-Skolem.
- **Key dependencies**:
  - SEM: PRIM-SEM011 (model), DEF-SEM008 (elementary equivalence), DEF-SEM014 (categoricity — for characterizing "more expressive")
  - SYN: PRIM-SYN009 (language), PRIM-SYN012 (formula)
  - BST: PRIM-BST016 (cardinality)
- **Proof sketch**: Define an "abstract logic" as a pair (sentences, satisfaction relation) satisfying certain closure conditions. Show that if a logic extends FOL and satisfies both compactness and DLS, then it has the same expressive power as FOL (every sentence is equivalent to a first-order sentence).
- **Source**: SRC-GLB015 (Lindstrom 1969)
- **Variant compatibility**: Characterizes classical FOL specifically. Does not directly apply to non-classical logics.
- **Significance**: Provides a mathematical justification for why FOL is the "natural" logic — it is the unique maximal logic with the good model-theoretic properties.

---

## 4. Variant Compatibility Matrix

| Pattern | Classical FOL | Intuitionistic | Modal | Many-valued | SOL (full) |
|---------|:---:|:---:|:---:|:---:|:---:|
| CP-001 Soundness | Y | Y | Y | Y | Y |
| CP-002 Completeness | Y | Y ^1 | Y ^2 | varies ^3 | N ^4 |
| CP-003 Compactness | Y | Y | Y | varies ^3 | N |
| CP-004 Lowenheim-Skolem | Y | N ^5 | limited ^6 | varies | N |
| CP-005 Godel I | Y | Y ^7 | N/A ^8 | N/A ^8 | Y |
| CP-006 Godel II | Y | Y ^7 | N/A ^8 | N/A ^8 | Y |
| CP-007 Undefinability | Y | Y | Y | varies | Y |
| CP-008 Church Undecidability | Y | Y | varies | varies | Y* |
| CP-009 Deduction Theorem | Y | Y | Y ^9 | Y | Y |
| CP-010 Cut Elimination | Y | Y | Y | Y | limited |
| CP-011 Interpolation | Y | Y | varies ^10 | varies | Y |
| CP-012 Beth Definability | Y | Y | varies | varies | Y |
| CP-013 Lindstrom | Y | N/A ^11 | N/A ^11 | N/A ^11 | N/A ^11 |

**Footnotes**:

1. **Intuitionistic completeness**: holds w.r.t. Kripke semantics (not classical Tarskian semantics).
2. **Modal completeness**: via canonical model construction; holds for many but not all normal modal logics (some are Kripke-incomplete).
3. **Many-valued**: depends on the specific semantics; finite-valued logics typically have completeness and compactness; some infinite-valued logics do not.
4. **SOL (full)**: Godel's completeness theorem fails for full second-order semantics. Only Henkin semantics (effectively first-order) has completeness.
5. **Intuitionistic L-S**: fails because intuitionistic logic lacks the classical witness property.
6. **Modal L-S**: limited forms hold for some modal logics but the standard theorem does not transfer directly.
7. **Intuitionistic incompleteness**: applies to Heyting Arithmetic (HA) — any sufficiently strong consistent intuitionistic theory is incomplete.
8. **Modal/Many-valued G1/G2**: not applicable in the standard sense — these logics don't typically formalize arithmetic internally.
9. **Modal deduction theorem**: holds with modifications (necessitation rule does not satisfy the standard deduction theorem form).
10. **Modal interpolation**: Craig interpolation fails for some normal modal logics (e.g., certain extensions of K).
11. **Lindstrom**: characterizes classical FOL specifically; the theorem does not directly apply to non-classical logics.

*SOL validity is $\Pi_1^1$-complete — not just undecidable but not even c.e.
