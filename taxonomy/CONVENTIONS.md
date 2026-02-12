# CONVENTIONS v0.1

This document establishes the cross-domain conventions, traceability infrastructure, and quality standards governing all taxonomy files. It MUST be read before any domain spec and MUST be complete before any domain spec is authored.

---

## 1. Foundational Principles

### Principle 1: Closed Domain Catalog, Open Pattern Catalog

The **domain catalog is closed**: 5 domains + BST. No 6th domain will be added. Any concept that appears to need a new domain MUST be resolved by: (a) assigning it to an existing domain via boundary principles (Section 5), or (b) documenting it as a composition pattern (Section 11).

The **composition pattern catalog is open**: new metatheorems, new cross-domain results, and new application-level patterns can be added indefinitely without restructuring the taxonomy.

New logics (modal, intuitionistic, etc.) are **extensions within existing domains**, not new domains. They plug in via documented extension points in each domain spec.

### Principle 2: Semi-Formal Specification Standard

Every primitive, definition, axiom, and theorem MUST have both:
- A **formal statement** using LaTeX math notation (`$...$` or `$$...$$`)
- A **natural language explanation** ($\geq 1$ complete sentence)

Every primitive and key definition MUST have $\geq 1$ **motivating example** — a concrete instance that makes the abstract concept tangible.

Notation follows standard mathematical logic conventions (Enderton, Mendelson). When conventions differ between sources, the chosen convention is noted with SRC reference.

**Balance**: formal notation for precision, prose for intuition, examples for grounding. If a reader with one semester of logic cannot parse a formal statement after reading its explanation and example, the explanation is insufficient.

### Principle 3: One Owner, Zero Redundancy

Every concept has **exactly one owning domain**. Other domains reference it, never redefine it. This is enforced by:
- Boundary principles P1--P5 (Section 5)
- Primitive Registry (Section 9)
- Redundancy detection procedure (Section 7)
- Self-audit checklists (Section 12)

### Principle 4: Divergences from Substrateresearch

The substrate methodology was designed for software systems. We adapt it for mathematics with these deliberate divergences:

| Substrate Feature | Logic Adaptation | Justification |
|---|---|---|
| Operational lifecycle (create/update/archive) | Not applicable | Mathematical objects are timeless; they don't have lifecycle states |
| Event bus (cross-substrate communication) | Static cross-domain references | Mathematical dependencies are permanent, not event-driven |
| Envelope chain (authority restriction) | Dependency DAG (prerequisite ordering) | Mathematics has prerequisites, not authority hierarchies |
| Concurrency & ordering | Not applicable | Mathematical proof is sequential; no concurrent access issues |
| Security & privacy | Not applicable | No sensitive data in pure mathematics |
| 24-section template | 13-section template | Sections for persistence, migration, operational profile, observability are irrelevant to mathematics |

What we **preserve fully**: Sources/Assumptions/Unknowns discipline. Normative language (MUST/SHOULD/MAY). Traceability IDs on every item. Boundary principles for ownership. Primitive ownership table. Gap analysis. Completeness checklist. Composition patterns.

---

## 2. Metatheory Stratification Protocol

This is the single most critical architectural decision. We operate at **two levels**:

### Level-0 (Metalanguage)

Naive set theory — sets, functions, relations, sequences, inductive definitions, natural numbers. Documented in `DOMAIN-SET-BOOTSTRAP.md` (code: BST). Used by SYNTAX (to define "the set of formulas"), SEMANTICS (to define structures/models), DEDUCTION (to define derivation sequences), and COMPUTATION (to define functions on $\mathbb{N}$).

This is NOT axiomatized. It is the ambient mathematical context, the same as any standard logic textbook uses.

**On naive power set**: BST includes "the collection of all subsets of $A$" as a naive concept, used to define things like "the set of all truth-value assignments." We do NOT claim this is constructive or justify it axiomatically — that is SET's job. BST simply notes: "We assume the standard mathematical practice of collecting subsets. Formal justification is provided by AX-SET004 (Power Set Axiom) in DOMAIN-SET-FORMAL.md."

### Level-1 (Object Language)

Formal set theory (ZFC) as a first-order theory within the taxonomy. Documented in `DOMAIN-SET-FORMAL.md` (code: SET). This is a specific first-order language ($\mathcal{L}_\in = \{\in\}$) + axiom system, analyzed using SYNTAX, SEMANTICS, and DEDUCTION from Level-0.

### Circularity Dissolution

Level-0 sets are used to BUILD the formalism. Level-1 set theory is a SUBJECT OF the formalism. They are not the same thing. (This mirrors Enderton Ch. 1, Shoenfield Ch. 1, and how Metamath handles its metalogic.)

### Distinguishing Meta-Level and Object-Level Concepts

Several terms appear at both levels and MUST be clearly separated:

| Concept | Level-0 (BST) | Level-1 (SYN/SEM/SET) |
|---------|---------------|----------------------|
| Function | A meta-mathematical mapping (e.g., interpretation function $f^{\mathfrak{A}}$) | A function symbol in the formal language (e.g., $f$ in $\mathcal{L}$) |
| Relation | A meta-mathematical relation (e.g., $R \subseteq A \times A$) | A relation symbol in the formal language (e.g., $R$ in $\mathcal{L}$) |
| Set | A naive collection (e.g., "the set of all formulas") | A formal object governed by ZFC axioms |
| Natural number | A meta-mathematical number used for counting (e.g., "arity 2") | A formal object in the theory of arithmetic ($\mathbb{N}$ as a structure) |

---

## 3. Traceability ID Scheme

### Domain Codes (unambiguous, 3-letter)

| Code | Domain |
|------|--------|
| BST | Set-Bootstrap (Level-0 naive sets) |
| SYN | Syntax |
| SEM | Semantics |
| DED | Deduction |
| CMP | Computation |
| SET | Set-Formal (Level-1 ZFC) |
| GLB | Global (shared references in this document) |

### Item Type Prefixes

| Prefix | Meaning | Example |
|--------|---------|---------|
| PRIM | Primitive notion (undefined) | PRIM-SYN001 |
| DEF | Definition (conservative extension) | DEF-SEM003 |
| AX | Axiom | AX-SET001 |
| THM | Theorem | THM-DED005 |
| SRC | Source reference | SRC-GLB001 (global) or SRC-SYN001 (domain-specific) |
| ASM | Assumption | ASM-GLB001 (global) or ASM-CMP001 (domain-specific) |
| UNK | Unknown / open question | UNK-SEM002 |
| DEP | Dependency on another domain | DEP-SEM001 |
| INV | Invariant (must always hold) | INV-SYN001 |
| FORBID | Forbidden state | FORBID-DED001 |
| EXT | Extension point | EXT-SYN001 |

### Cross-Domain Reference Format

References use the format `{ItemType}-{DomainCode}{Number}`. When domain A references domain B's primitive, write `PRIM-BST003` (not a local alias). The owning domain MUST list it in Exports; the referencing domain MUST list it in Imports.

### Source Reference Scoping

Global SRC entries (SRC-GLB001 through SRC-GLBNNN) live in this document and are shared across all domain specs. Domain-specific SRC entries (SRC-{D}NNN) live in their domain spec for sources relevant only to that domain. Domain specs MAY cite global SRCs by their GLB ID.

### ID Stability

IDs are permanent once assigned. Deprecated items use `DEPRECATED-{original-ID}` with pointer to replacement. IDs MUST NOT be renumbered across versions.

### Document Versioning

Domain specs use semantic versioning (v0.1 $\to$ v0.2 for non-breaking additions, v1.0 for first stable release). Breaking changes (removing/renaming primitives) require v(N+1).0 and a migration note listing all affected cross-references.

### Reserved ID Ranges for Future Extensions

- `*-{DOM}001--099`: Classical core
- `*-{DOM}100--199`: Modal extensions
- `*-{DOM}200--299`: Intuitionistic extensions
- `*-{DOM}300--399`: Higher-order extensions
- `*-{DOM}400--499`: Substructural extensions
- `*-{DOM}500--599`: Many-valued extensions

---

## 4. Normative Language

Per RFC 2119, used at full strength throughout all taxonomy documents:

- **MUST** / **MUST NOT** = axiom-level; violation means the system is inconsistent or the taxonomy is structurally broken
- **SHOULD** / **SHOULD NOT** = strong convention; deviation requires documented justification
- **MAY** = optional; extension point or variant-specific

---

## 5. Boundary Principles (Ownership Disambiguation)

When a concept could belong to multiple domains, these principles resolve ownership:

| Principle | Rule | Example |
|-----------|------|---------|
| **P1 — Formation vs. Interpretation** | If definable purely via symbol manipulation without truth/meaning $\to$ SYN. If requires interpretation $\to$ SEM. | "formula" $\to$ SYN. "satisfaction" $\to$ SEM. |
| **P2 — Derivation vs. Truth** | Syntactic consequence ($\vdash$) $\to$ DED. Semantic consequence ($\vDash$) $\to$ SEM. Results connecting them $\to$ composition patterns. | "proof" $\to$ DED. "validity" $\to$ SEM. "soundness" $\to$ CP-001. |
| **P3 — Effective vs. Abstract** | If inherently involves effective procedures / algorithms $\to$ CMP. If involves arbitrary existence $\to$ SET or BST. | "decidable set" $\to$ CMP. "power set" $\to$ BST (naive) / SET (formal). |
| **P4 — One Owner, Many References** | Every primitive has exactly one owner. Others reference via cross-domain format. | See pre-analyzed splits below. |
| **P5 — Bootstrap vs. Formal** | Naive metalanguage concepts $\to$ BST. Axiomatized formal concepts $\to$ SET. | "the set of all formulas" $\to$ BST. "the axiom of infinity" $\to$ SET. |

### Pre-Analyzed Ownership Splits for Contested Concepts

| Concept | Syntactic Version (Owner) | Semantic Version (Owner) | Connection |
|---------|--------------------------|-------------------------|------------|
| Consistency | "No derivation of $\varphi \land \neg\varphi$" $\to$ **DED** (DEF-DED) | "Has a model" $\to$ **SEM** (DEF-SEM) | Linked by CP-001 (Soundness) + CP-002 (Completeness) |
| Validity | N/A | "$\vDash \varphi$ (true in all structures)" $\to$ **SEM** (DEF-SEM) | DED aims to derive valid formulas; validity itself is semantic |
| Substitution | "$\varphi[t/x]$ (replacing $x$ by $t$ in $\varphi$)" $\to$ **SYN** (DEF-SYN) | Referenced by SEM (variable assignment) and DED (rule application) | SYN owns the operation; SEM and DED reference it |
| Theory | N/A | "$\text{Th}(\mathfrak{A}) = \{\varphi : \mathfrak{A} \vDash \varphi\}$" $\to$ **SEM** (DEF-SEM) | DED references when discussing "deductively closed sets" |
| Completeness (of a theory) | N/A | "For all sentences $\varphi$: $T \vDash \varphi$ or $T \vDash \neg\varphi$" $\to$ **SEM** (DEF-SEM) | Not the same as the Completeness Theorem (CP-002) |
| Decidability | N/A | "Decidable theory" = theory whose set of theorems is decidable $\to$ **CMP** (DEF-CMP) | CMP owns the concept; SEM and DED reference it. Boundary: P3. |
| Axiom | "Axiom schema" / "logical axiom" (rule in a proof system) $\to$ **DED** (PRIM-DED) | "ZFC axiom" (formal constraint in a first-order theory) $\to$ **SET** (AX-SET) | DED axioms are proof-system rules; SET axioms are theory-specific postulates. Boundary: P2 vs P5. |
| Modus Ponens | A specific named rule of inference $\to$ **DED** (AX-DED, not PRIM) | N/A | MP is an instance of the PRIM "rule of inference," formalized as AX-DED. |

---

## 6. Non-Classical Logics: Extension Protocol

The 5 domains define the **abstract pattern** all logics share. Classical FOL is the **primary instantiation**. Extensions come in three types:

| Extension Type | What Changes | Examples |
|---------------|-------------|----------|
| **Additive** | New operators/semantic structures added, classical core preserved | Modal ($\Box$/$\Diamond$ + Kripke frames), temporal, deontic, epistemic |
| **Replacement** | Core semantic or proof-theoretic machinery replaced | Intuitionistic (BHK replaces Tarski; no LEM), many-valued (truth set $\neq \{0,1\}$) |
| **Structural** | Structural rules of proof systems modified | Linear logic (no contraction/weakening), relevance logic |

### How to Add a New Logic Variant

1. Identify which domains are affected and which extension type applies (additive/replacement/structural)
2. For each affected domain, allocate IDs in the reserved range (`*-{DOM}100--199` for modal, `200--299` for intuitionistic, etc.)
3. For additive extensions: add new PRIM/DEF/AX entries with "Extends: PRIM-{DOM}NNN" annotations
4. For replacement extensions: create parallel entries (e.g., PRIM-SEM201: "BHK satisfaction" alongside PRIM-SEM005: "Tarski satisfaction") with explicit notes on which is active in which variant
5. **If the extension requires BST concepts not already in BST** (e.g., accessibility relations for modal logic): add them as new BST primitives, not as domain-specific primitives, to maintain metalanguage universality
6. Update the Variant Compatibility Matrix in CROSS-DOMAIN-MAP.md
7. Run the self-audit checklist for all affected domain specs

### Propositional Logic as Restricted Fragment

PL is handled as a **restricted fragment** within each domain: SYN-PL (no quantifiers/terms), SEM-PL (truth-value assignments, not structures), DED-PL (propositional rules only). Each domain spec annotates which primitives belong to the propositional fragment via the `Fragment:` field.

**Self-coherence requirement**: The PL fragment MUST be self-coherent — a reader should be able to extract only PL-annotated items from SYN, SEM, and DED and obtain a complete, self-contained propositional logic sub-taxonomy.

### Second-Order and Higher-Order Logics

These modify SYNTAX fundamentally (variables range over predicates/functions) and break key metatheoretic composition results (no completeness theorem for full SOL). Documented as a named "higher-order tier" with explicit notes on which composition patterns survive.

---

## 7. Redundancy Detection Procedure

Run **after completing each domain spec** (partial check against existing registry) and **in full during the Reconciliation Pass** (Step 9):

1. **Alphabetical cross-domain sort**: Export all PRIM and DEF entries from all domains into a single list sorted by concept name. Flag any name appearing in more than one domain.
2. **For each flagged name**: Apply boundary principles P1--P5. Determine: is this genuinely two different concepts (like syntactic vs. semantic consistency), or an ownership violation (same concept defined twice)?
3. **If two different concepts**: Ensure both have distinct names (e.g., "syntactic consistency" vs. "semantic consistency"), distinct IDs, and a documented cross-reference linking them via a composition pattern.
4. **If ownership violation**: Remove the duplicate from the non-owning domain. Replace with a REFERENCES annotation pointing to the owner's ID.
5. **Registry update**: After resolution, update the Primitive Registry (Section 9).

---

## 8. Iteration and Backtracking Protocol

Writing domain specs is not purely linear. When Step N reveals a needed change to Step M (M < N):

1. **Identify the change**: What primitive/definition/axiom in domain M needs to be added, modified, or have its ownership changed?
2. **Update domain M's spec**: Make the change, update the Primitive Registry, increment version (v0.1 $\to$ v0.2).
3. **Cascade check**: Search all domain specs written between M and N for references to the changed item. Update cross-references.
4. **Re-run self-audit**: Run the 12-item checklist on both the modified domain M and any domains with updated cross-references.
5. **Continue**: Resume Step N with the fix in place.

The Reconciliation Pass (Step 9) is the scheduled iteration point, but backtracking MAY happen at any step.

---

## 9. Primitive Registry

Single source of truth for all primitives and definitions across the taxonomy. Updated after each domain spec is completed.

| ID | Concept | Owner Domain | Referenced By |
|----|---------|-------------|---------------|
| PRIM-BST001 | Set | BST | SYN, SEM, DED, CMP, SET |
| PRIM-BST002 | Membership ($\in$) | BST | SYN, SEM, DED, CMP, SET |
| PRIM-BST003 | Subset ($\subseteq$) | BST | SEM, SET |
| PRIM-BST004 | Empty Set ($\emptyset$) | BST | SEM, DED, SET |
| PRIM-BST005 | Union/Intersection ($\cup$/$\cap$) | BST | SYN, SEM, DED |
| PRIM-BST006 | Ordered Pair ($\langle a, b \rangle$) | BST | SEM, DED, CMP |
| PRIM-BST007 | Cartesian Product ($A \times B$) | BST | SEM, DED, CMP |
| PRIM-BST008 | Relation | BST | SYN, SEM, CMP |
| PRIM-BST009 | Function | BST | SYN, SEM, DED, CMP |
| PRIM-BST010 | Finite Sequence | BST | SYN, DED, CMP |
| PRIM-BST011 | Infinite Sequence | BST | SEM, CMP |
| PRIM-BST012 | Natural Number ($\mathbb{N}$) | BST | SYN, SEM, DED, CMP, SET |
| PRIM-BST013 | Mathematical Induction | BST | SYN, SEM, DED, CMP |
| PRIM-BST014 | Inductive Definition | BST | SYN, SEM, DED, CMP |
| PRIM-BST015 | Power Set (naive, $\mathcal{P}(A)$) | BST | SEM, SET |
| PRIM-BST016 | Cardinality (finite/countable/uncountable) | BST | SEM, CMP, SET |
| DEF-BST001 | Injection | BST | SEM, CMP, SET |
| DEF-BST002 | Surjection | BST | SEM, CMP |
| DEF-BST003 | Bijection | BST | SEM, CMP, SET |
| DEF-BST004 | Equivalence Relation | BST | SEM, SYN |
| DEF-BST005 | Partial Order | BST | SET, SEM |
| PRIM-SYN001 | Symbol | SYN | SEM, DED, CMP |
| PRIM-SYN002 | Variable | SYN | SEM, DED, CMP |
| PRIM-SYN003 | Logical Connective | SYN | SEM, DED |
| PRIM-SYN004 | Quantifier | SYN | SEM, DED |
| PRIM-SYN005 | Constant Symbol | SYN | SEM |
| PRIM-SYN006 | Function Symbol | SYN | SEM |
| PRIM-SYN007 | Relation Symbol (Predicate Symbol) | SYN | SEM |
| PRIM-SYN008 | Arity | SYN | SEM |
| PRIM-SYN009 | Language (Signature) | SYN | SEM, DED, CMP, SET |
| PRIM-SYN010 | Term | SYN | SEM, DED |
| PRIM-SYN011 | Atomic Formula | SYN | SEM, DED |
| PRIM-SYN012 | Formula (wff) | SYN | SEM, DED, CMP |
| PRIM-SYN013 | Sentence | SYN | SEM, DED, CMP |
| PRIM-SYN014 | Free Occurrence | SYN | SEM, DED |
| PRIM-SYN015 | Bound Occurrence | SYN | SEM, DED |
| PRIM-SYN016 | Scope | SYN | SEM, DED |
| PRIM-SYN017 | Subformula | SYN | SEM, DED |
| PRIM-SYN018 | Equality Symbol ($=$) | SYN | SEM, DED, SET |
| DEF-SYN001 | Substitution ($\varphi[t/x]$) | SYN | SEM, DED |
| DEF-SYN002 | Simultaneous Substitution | SYN | SEM, DED |
| DEF-SYN003 | Free Variables ($\text{FV}$) | SYN | SEM, DED |
| DEF-SYN004 | Alphabetic Variant | SYN | SEM, DED |
| DEF-SYN005 | Structural Induction on Formulas | SYN | SEM, DED |
| DEF-SYN006 | Structural Recursion on Formulas | SYN | SEM, CMP |
| DEF-SYN007 | Formula Complexity (Rank) | SYN | SEM, DED |
| DEF-SYN008 | Subterm | SYN | SEM |
| PRIM-SEM001 | Structure ($\mathfrak{A}$) | SEM | DED, SET, CMP |
| PRIM-SEM002 | Domain ($\|\mathfrak{A}\|$) | SEM | DED, CMP |
| PRIM-SEM003 | Interpretation | SEM | DED |
| PRIM-SEM004 | Variable Assignment ($s$) | SEM | DED |
| PRIM-SEM005 | $x$-Variant of Assignment | SEM | DED |
| PRIM-SEM006 | Term Valuation | SEM | DED |
| PRIM-SEM007 | Satisfaction ($\mathfrak{A} \vDash \varphi[s]$) | SEM | DED, CMP |
| PRIM-SEM008 | Truth in a Structure ($\mathfrak{A} \vDash \varphi$) | SEM | DED, CMP |
| PRIM-SEM009 | Logical Validity ($\vDash \varphi$) | SEM | DED, CMP |
| PRIM-SEM010 | Logical Consequence ($\Gamma \vDash \varphi$) | SEM | DED |
| PRIM-SEM011 | Model ($\mathfrak{A} \vDash T$) | SEM | DED, SET, CMP |
| PRIM-SEM012 | Isomorphism ($\mathfrak{A} \cong \mathfrak{B}$) | SEM | SET, CMP |
| PRIM-SEM013 | Substructure | SEM | SET |
| PRIM-SEM014 | Homomorphism | SEM | SET |
| PRIM-SEM015 | Truth-Value Assignment (PL) | SEM | DED |
| DEF-SEM001 | Tarski Satisfaction Definition | SEM | DED, CMP |
| DEF-SEM002 | Satisfiable | SEM | DED |
| DEF-SEM003 | Finitely Satisfiable | SEM | DED |
| DEF-SEM004 | Semantic Consistency | SEM | DED |
| DEF-SEM005 | Semantic Completeness (of a theory) | SEM | DED, CMP |
| DEF-SEM006 | Theory of a Structure ($\text{Th}(\mathfrak{A})$) | SEM | DED, CMP |
| DEF-SEM007 | Definable Set | SEM | CMP, SET |
| DEF-SEM008 | Elementary Equivalence ($\equiv$) | SEM | CMP |
| DEF-SEM009 | Tautology (PL Validity) | SEM | DED |
| DEF-SEM010 | PL Consequence | SEM | DED |
| DEF-SEM011 | Elementary Substructure ($\preccurlyeq$) | SEM | SET |
| DEF-SEM012 | Diagram (Atomic/Elementary) | SEM | DED |
| DEF-SEM013 | Type (Complete Type) | SEM | — |
| DEF-SEM014 | Categoricity ($\kappa$-categorical) | SEM | SET |
| DEF-SEM015 | Ultraproduct | SEM | SET |
| DEF-SEM016 | Embedding | SEM | SET |
| PRIM-DED001 | Axiom Schema | DED | SEM, CMP |
| PRIM-DED002 | Non-Logical Axiom | DED | SEM, SET |
| PRIM-DED003 | Rule of Inference | DED | SEM, CMP |
| PRIM-DED004 | Proof System | DED | SEM, CMP |
| PRIM-DED005 | Derivation | DED | SEM, CMP |
| PRIM-DED006 | Provability ($\Gamma \vdash \varphi$) | DED | SEM, CMP |
| PRIM-DED007 | Structural Rule | DED | — |
| PRIM-DED008 | Sequent ($\Gamma \Rightarrow \Delta$) | DED | — |
| PRIM-DED009 | Assumption Discharge | DED | — |
| PRIM-DED010 | Theorem | DED | SEM, CMP |
| DEF-DED001 | Syntactic Consistency | DED | SEM, CMP |
| DEF-DED002 | Maximal Consistent Set | DED | SEM |
| DEF-DED003 | Deductive Closure ($\text{Cn}$) | DED | SEM |
| DEF-DED004 | Conservative Extension | DED | SET, CMP |
| DEF-DED005 | Hilbert-Style System | DED | SEM, CMP |
| DEF-DED006 | Natural Deduction | DED | SEM, CMP |
| DEF-DED007 | Sequent Calculus | DED | SEM |
| DEF-DED008 | Tableau System | DED | CMP |
| DEF-DED009 | Derived Rule | DED | — |
| DEF-DED010 | Admissible Rule | DED | — |
| PRIM-CMP001 | Computable (Recursive) Function | CMP | SEM, DED, SET |
| PRIM-CMP002 | Primitive Recursive Function | CMP | DED, SET |
| PRIM-CMP003 | $\mu$-Recursion | CMP | DED |
| PRIM-CMP004 | Turing Machine | CMP | SEM, DED |
| PRIM-CMP005 | Church-Turing Thesis | CMP | SEM, DED |
| PRIM-CMP006 | Decidable Set | CMP | SEM, DED |
| PRIM-CMP007 | Semi-Decidable (c.e.) Set | CMP | DED |
| PRIM-CMP008 | Halting Problem | CMP | SEM, DED |
| PRIM-CMP009 | Many-One Reducibility ($\leq_m$) | CMP | SEM |
| PRIM-CMP010 | Diagonalization | CMP | SEM, DED |
| PRIM-CMP011 | Godel Numbering (Arithmetization) | CMP | SYN, DED, SEM |
| PRIM-CMP012 | Universal Turing Machine | CMP | DED |
| DEF-CMP001 | Partial Function | CMP | DED, SEM |
| DEF-CMP002 | Total Function | CMP | SEM |
| DEF-CMP003 | Characteristic Function ($\chi_A$) | CMP | DED |
| DEF-CMP004 | Enumeration | CMP | DED |
| DEF-CMP005 | Index (Program) | CMP | DED |
| DEF-CMP006 | Lambda-Definable Function | CMP | DED |
| DEF-CMP007 | Productive Set | CMP | — |
| DEF-CMP008 | Creative Set | CMP | — |
| DEF-CMP009 | Representability | CMP | DED, SEM |
| DEF-CMP010 | Recursive Enumerability (equiv. char.) | CMP | DED |
| PRIM-SET001 | Set (formal) | SET | SEM |
| PRIM-SET002 | Membership ($\in$, formal) | SET | SYN |
| PRIM-SET003 | Class (informal) | SET | — |
| DEF-SET001 | Ordinal Number (von Neumann) | SET | SEM |
| DEF-SET002 | Successor Ordinal | SET | — |
| DEF-SET003 | Limit Ordinal | SET | — |
| DEF-SET004 | $\omega$ | SET | SEM, CMP |
| DEF-SET005 | Transfinite Induction | SET | SEM |
| DEF-SET006 | Transfinite Recursion | SET | SEM |
| DEF-SET007 | Cardinal Number | SET | SEM |
| DEF-SET008 | Cardinality (formal) | SET | SEM |
| DEF-SET009 | Well-Ordering | SET | SEM |
| DEF-SET010 | Zorn's Lemma | SET | DED, SEM |
| DEF-SET011 | Cantor's Theorem (formal) | SET | SEM |

---

## 10. Domain Dependency DAG

```
BST (Level-0 root, no prerequisites)
 +-- SYN (depends: BST)
 |    +-- SEM (depends: SYN, BST)
 |    +-- DED (depends: SYN, BST)
 +-- CMP (depends: BST)
 +-- SET (depends: SYN, SEM, DED, BST)
```

SET depends on the full metatheoretic apparatus because it is a first-order theory analyzed using SYN (its language $\mathcal{L}_\in$), SEM (its models), and DED (proofs within ZFC).

---

## 11. Composition Pattern Template

Composition patterns document metatheorems that live at domain intersections. Each pattern follows this format:

```markdown
### CP-NNN: **{Pattern Name}**

- **Domains**: {DomainCode} x {DomainCode} [x ...]
- **Statement**: [semi-formal statement with LaTeX math]
- **Natural language**: [explanation, >= 1 sentence]
- **Key dependencies**: [list of PRIM/DEF/AX IDs from each involved domain]
- **Proof sketch**: [outline or reference to standard proof]
- **Source**: SRC-GLBNNN or SRC-{D}NNN
- **Variant compatibility**: [which logic variants preserve this pattern; see Variant Compatibility Matrix]
- **Significance**: [why this result matters for the taxonomy]
```

---

## 12. Self-Audit Checklist

Every domain spec MUST pass all 12 items before being considered complete:

- [ ] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [ ] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [ ] Every THM depends only on previously listed AX/DEF/THM
- [ ] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [ ] Every import is listed in the source domain's exports
- [ ] Dissolution argument is present and non-trivial
- [ ] Extension points cover all three types (additive/replacement/structural) where applicable
- [ ] Intra-domain dependency graph is acyclic
- [ ] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [ ] Motivating examples are present for all PRIM and key DEF entries
- [ ] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [ ] Completeness argument addresses all relevant OL chapters

---

## 13. Global Sources (SRC-GLB)

| ID | Reference |
|----|-----------|
| SRC-GLB001 | Enderton, *A Mathematical Introduction to Logic*, 2nd ed., 2001 |
| SRC-GLB002 | Shoenfield, *Mathematical Logic*, 1967 |
| SRC-GLB003 | Mendelson, *Introduction to Mathematical Logic*, 6th ed., 2015 |
| SRC-GLB004 | Tarski, "The concept of truth in formalized languages," 1935 |
| SRC-GLB005 | Godel, "On formally undecidable propositions," 1931 |
| SRC-GLB006 | Church, "An unsolvable problem of elementary number theory," 1936 |
| SRC-GLB007 | Turing, "On computable numbers, with an application to the Entscheidungsproblem," 1936 |
| SRC-GLB008 | Kleene, *Introduction to Metamathematics*, 1952 |
| SRC-GLB009 | Gentzen, "Investigations into logical deduction," 1935 |
| SRC-GLB010 | Zermelo, "Investigations in the foundations of set theory I," 1908 |
| SRC-GLB011 | Kripke, "Semantical considerations on modal logic," 1963 |
| SRC-GLB012 | Heyting, *Intuitionism: An Introduction*, 1956 |
| SRC-GLB013 | Chang & Keisler, *Model Theory*, 3rd ed., 1990 |
| SRC-GLB014 | Marker, *Model Theory: An Introduction*, 2002 |
| SRC-GLB015 | Lindstrom, "On extensions of elementary logic," 1969 |

---

## 14. Global Assumptions (ASM-GLB)

| ID | Assumption | Justification |
|----|-----------|---------------|
| ASM-GLB001 | Classical logic is the primary instantiation; non-classical logics are extensions | Matches standard curriculum; classical FOL is the foundation all others are defined against |
| ASM-GLB002 | The metalanguage uses naive set theory (Level-0) without formal justification | Standard practice in all major logic textbooks (Enderton, Shoenfield, Mendelson); formal foundations come later via SET |
| ASM-GLB003 | Readers have at least one semester of logic or equivalent mathematical maturity | This is a reference taxonomy, not a first course; prerequisite knowledge includes basic proof techniques and mathematical notation |
| ASM-GLB004 | English is the metalanguage; formulas use standard notation ($\neg, \to, \land, \lor, \forall, \exists$) | Matches OpenLogic and major textbooks; notation variants are noted where they exist |
| ASM-GLB005 | We scope computability and set theory to "for logic" — only what's needed for metatheorems | Prevents Phase 1 from expanding into an encyclopedia of recursion theory or set theory |

---

## 15. Global Unknowns (UNK-GLB)

| ID | Unknown | Impact |
|----|---------|--------|
| UNK-GLB001 | Optimal granularity for connectives: should "connective" be one primitive or should $\neg$, $\to$, $\land$, $\lor$, $\leftrightarrow$ each be separate? | Affects primitive count and traceability granularity. Resolve during DOMAIN-SYNTAX authoring. |
| UNK-GLB002 | Should proof system architectures (Hilbert, ND, SC, Tableaux) be parallel PRIM entries or parameterized variants of a single DEF? | Affects DED structure. Resolve during DOMAIN-DEDUCTION authoring. |
| UNK-GLB003 | How deep into model theory should SEM go? | Managed by the SEM triage strategy: if SEM exceeds 30 items, split into core + model theory supplement. |

---

## 16. Worked Example: One Fully Specified Entry

This demonstrates exactly what a completed entry looks like in a domain spec:

- AX-DED001: **Modus Ponens (MP)**
  - Statement: If $\Gamma \vdash \varphi$ and $\Gamma \vdash (\varphi \to \psi)$, then $\Gamma \vdash \psi$.
  - Description: The rule of inference that, given a derivation of $\varphi$ and a derivation of $\varphi \to \psi$, produces a derivation of $\psi$. It is the fundamental elimination rule for the conditional connective. MP is a specific named instance of the primitive PRIM-DED003 (rule of inference).
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED006 (provability), PRIM-SYN003 (logical connective, specifically $\to$)
  - Source: SRC-GLB001 (Enderton 2.4), SRC-GLB009 (Gentzen, as "$\to$-elimination")
  - Normative: MUST (every Hilbert-style system includes MP)
  - Natural language: Given any two already-derived statements where one is "if A then B" and the other is "A," you may derive "B."
  - Motivating example: From "It is raining" ($p$) and "If it is raining then the ground is wet" ($p \to q$), derive "The ground is wet" ($q$). Formally: from $\{p, p \to q\} \vdash p$ and $\{p, p \to q\} \vdash (p \to q)$, conclude $\{p, p \to q\} \vdash q$.

Every item in every domain spec MUST match this level of detail.
