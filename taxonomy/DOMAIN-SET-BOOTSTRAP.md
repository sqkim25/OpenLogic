# DOMAIN-SET-BOOTSTRAP v0.1

## 0. Sources & Assumptions

- SRC-BST001: Halmos, *Naive Set Theory*, 1960
- SRC-BST002: Enderton, *Elements of Set Theory*, 1977 (Ch. 1--3 for naive exposition)
- ASM-BST001: We work in naive set theory as our metalanguage. No axiomatization is given or required. This is the ambient mathematical context shared by all standard logic textbooks. Justification: ASM-GLB002.
- ASM-BST002: We assume the existence of the natural numbers $\mathbb{N} = \{0, 1, 2, \ldots\}$ as a completed totality, available for indexing, counting, and inductive arguments. Justification: standard mathematical practice; formal justification via AX-SET005 (Axiom of Infinity) in DOMAIN-SET-FORMAL.md.
- ASM-BST003: We assume the principle of mathematical induction on $\mathbb{N}$ is valid. Justification: inherent in the structure of $\mathbb{N}$; formalized in SET.
- UNK-BST001: Should "string" (finite sequence of symbols) be a BST primitive or a SYN primitive? Impact: affects whether SYN depends on BST for the notion of "string" or introduces it independently. Resolution: treated as a specialization of PRIM-BST009 (finite sequence) — SYN imports it. Resolved.

## 1. Domain Intent

- **Irreducible question**: What naive mathematical objects does the metalanguage use?
- **Scope**: The pre-formal mathematical substrate consumed by all other domains. Sets, functions, relations, sequences, natural numbers, induction, and cardinality concepts — all at the naive/intuitive level.
- **Non-goals**: Axiomatization of set theory (that is SET). Ordinals, cardinals beyond countable/uncountable (that is SET). Transfinite induction, axiom of choice, well-ordering theorem (that is SET). Any notion that requires a formal language or formal proof system.
- **Dissolution argument**: Naive set concepts (set, function, sequence, induction) are shared infrastructure consumed by ALL other domains. Without BST, every domain would independently introduce "set," "function," "sequence" — causing massive redundancy. BST factors out the common mathematical substrate. BST cannot be merged into SET because BST is un-axiomatized metalanguage while SET is a formal first-order theory (see Level-0/Level-1 distinction in CONVENTIONS.md Section 2). BST is the language we use to TALK ABOUT formal systems; SET is a formal system we talk about.

## 2. Prerequisites

None. BST is the root of the dependency DAG. It has no formal prerequisites — it IS the prerequisite infrastructure for everything else.

## 3. Primitive Notions

- PRIM-BST001: **Set**
  - Description: A collection of objects, called elements or members, treated as a single entity. A set is determined entirely by its members — two sets are equal if and only if they have exactly the same members.
  - Formal: $A, B, C, \ldots$ denote sets. $A = B \iff \forall x\,(x \in A \leftrightarrow x \in B)$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 1), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SYN (set of symbols, set of formulas), SEM (domain of a structure, set of truth values), DED (set of assumptions, set of theorems), CMP (set of natural numbers, decidable sets), SET (formal set as object of study)
  - Fragment: both
  - Motivating example: $\{a, b, c\}$ is a set with three elements. $\{x : x \text{ is a prime number less than 10}\} = \{2, 3, 5, 7\}$.

- PRIM-BST002: **Membership ($\in$)**
  - Description: The fundamental relation between an object and a set. "$a \in A$" means "$a$ is an element of $A$." This is the sole primitive relation of set theory at both Level-0 and Level-1, though at Level-0 it is understood naively.
  - Formal: $a \in A$ (read: "$a$ is a member of $A$" or "$a$ belongs to $A$").
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 1), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SYN (symbol membership in alphabet), SEM (element of a domain), DED (formula membership in assumption set), CMP (membership in decidable sets), SET (formal $\in$ relation)
  - Fragment: both
  - Motivating example: $3 \in \{1, 2, 3\}$ is true. $4 \in \{1, 2, 3\}$ is false.

- PRIM-BST003: **Subset ($\subseteq$)**
  - Description: A set $A$ is a subset of a set $B$ if every element of $A$ is also an element of $B$.
  - Formal: $A \subseteq B \iff \forall x\,(x \in A \to x \in B)$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 1)
  - Referenced by: SEM (substructures), SET (subset relation in formal set theory)
  - Fragment: both
  - Motivating example: $\{1, 2\} \subseteq \{1, 2, 3\}$. Every set is a subset of itself.

- PRIM-BST004: **Empty Set ($\emptyset$)**
  - Description: The unique set with no elements. It is a subset of every set.
  - Formal: $\emptyset = \{\}$; $\forall x\,(x \notin \emptyset)$; $\forall A\,(\emptyset \subseteq A)$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 1)
  - Referenced by: SEM (empty domain — noting that standard FOL requires non-empty domains), DED (empty assumption set), SET (formal existence via Separation)
  - Fragment: both
  - Motivating example: The set of all integers that are both even and odd is $\emptyset$.

- PRIM-BST005: **Union ($\cup$) and Intersection ($\cap$)**
  - Description: The union of sets $A$ and $B$ is the set of all objects belonging to at least one of them. The intersection is the set of all objects belonging to both.
  - Formal: $A \cup B = \{x : x \in A \lor x \in B\}$; $A \cap B = \{x : x \in A \land x \in B\}$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 2--4)
  - Referenced by: SYN (union of alphabets for combined languages), SEM (union of domains), DED (union of assumption sets)
  - Fragment: both
  - Motivating example: $\{1, 2\} \cup \{2, 3\} = \{1, 2, 3\}$. $\{1, 2\} \cap \{2, 3\} = \{2\}$.

- PRIM-BST006: **Ordered Pair ($\langle a, b \rangle$)**
  - Description: An object that encodes two objects in a specific order, such that $\langle a, b \rangle = \langle c, d \rangle$ if and only if $a = c$ and $b = d$. The standard Kuratowski encoding is $\langle a, b \rangle = \{\{a\}, \{a, b\}\}$, but at Level-0 we require only the characteristic property.
  - Formal: $\langle a, b \rangle$ with $\langle a, b \rangle = \langle c, d \rangle \iff (a = c \land b = d)$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 6), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SEM (interpretation pairs), DED (sequent pairs), CMP (input-output pairs)
  - Fragment: both
  - Motivating example: $\langle 1, 2 \rangle \neq \langle 2, 1 \rangle$. The ordered pair records which is "first" and which is "second."

- PRIM-BST007: **Cartesian Product ($A \times B$)**
  - Description: The set of all ordered pairs whose first component is from $A$ and whose second component is from $B$.
  - Formal: $A \times B = \{\langle a, b \rangle : a \in A \land b \in B\}$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 6)
  - Referenced by: SEM (product domains, relation as subset of product), DED (derivation trees), CMP (multi-argument functions)
  - Fragment: both
  - Motivating example: $\{0, 1\} \times \{a, b\} = \{\langle 0, a \rangle, \langle 0, b \rangle, \langle 1, a \rangle, \langle 1, b \rangle\}$.

- PRIM-BST008: **Relation**
  - Description: A set of ordered pairs. An $n$-ary relation on $A$ is a subset of $A^n$ (the $n$-fold Cartesian product of $A$ with itself). A binary relation on $A$ is a subset of $A \times A$.
  - Formal: $R \subseteq A \times B$ (binary); $R \subseteq A_1 \times \cdots \times A_n$ ($n$-ary).
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 7), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SEM (interpretation of relation symbols, satisfaction relation), SYN (relation symbols in a language), CMP (computable relations)
  - Fragment: both
  - Motivating example: The "less than" relation on $\mathbb{N}$ is $\{(m, n) \in \mathbb{N} \times \mathbb{N} : m < n\} = \{\langle 0, 1 \rangle, \langle 0, 2 \rangle, \langle 1, 2 \rangle, \ldots\}$.

- PRIM-BST009: **Function**
  - Description: A relation $f \subseteq A \times B$ such that for every $a \in A$ there exists exactly one $b \in B$ with $\langle a, b \rangle \in f$. We write $f : A \to B$ and $f(a) = b$. $A$ is the domain, $B$ is the codomain.
  - Formal: $f : A \to B$ where $\forall a \in A\,\exists! b \in B\,(\langle a, b \rangle \in f)$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 8), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SYN (function symbols, arity as function), SEM (interpretation functions, variable assignments), DED (derivation functions), CMP (computable functions, partial functions)
  - Fragment: both
  - Motivating example: The successor function $s : \mathbb{N} \to \mathbb{N}$ defined by $s(n) = n + 1$. The interpretation of a binary function symbol $f$ in a structure $\mathfrak{A}$ is a function $f^{\mathfrak{A}} : |\mathfrak{A}|^2 \to |\mathfrak{A}|$.

- PRIM-BST010: **Sequence (Finite)**
  - Description: A finite ordered list of objects. Formally, a function from $\{1, \ldots, n\}$ (or $\{0, \ldots, n-1\}$) to some set. The length $n$ is a natural number. Strings (finite sequences of symbols) are a key special case.
  - Formal: $\langle a_1, a_2, \ldots, a_n \rangle$ is a function $f : \{1, \ldots, n\} \to A$ with $f(i) = a_i$.
  - Ownership: OWNS
  - Source: SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SYN (strings of symbols, terms, formulas as finite sequences), DED (derivations as finite sequences of formulas), CMP (inputs/outputs as finite strings)
  - Fragment: both
  - Motivating example: The string "$\forall x\, P(x)$" is a finite sequence of symbols. A derivation in a Hilbert system is a finite sequence $\langle \varphi_1, \varphi_2, \ldots, \varphi_n \rangle$ of formulas.

- PRIM-BST011: **Sequence (Infinite)**
  - Description: A function from $\mathbb{N}$ (or an initial segment of ordinals) to some set. Infinite sequences are needed for semantic constructions (e.g., variable assignments, Henkin constructions) and computability (e.g., Turing machine computations as infinite sequences of configurations).
  - Formal: $\langle a_0, a_1, a_2, \ldots \rangle$ is a function $f : \mathbb{N} \to A$ with $f(i) = a_i$.
  - Ownership: OWNS
  - Source: SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SEM (variable assignments as functions from variables to domain elements), CMP (computation sequences, enumerations)
  - Fragment: FOL (PL does not require infinite sequences for its basic development)
  - Motivating example: A variable assignment $s : \text{Var} \to |\mathfrak{A}|$ assigns a domain element to each variable, forming a (potentially infinite) sequence.

- PRIM-BST012: **Natural Number ($\mathbb{N}$)**
  - Description: The natural numbers $0, 1, 2, \ldots$ as a completed collection. Used for counting (arity, formula length, proof length), indexing (variable subscripts, sequence positions), and as the domain for induction and recursion. At Level-0, we take $\mathbb{N}$ as given; its formal construction is in SET.
  - Formal: $\mathbb{N} = \{0, 1, 2, 3, \ldots\}$ with successor $s(n) = n + 1$, addition, and multiplication.
  - Ownership: OWNS
  - Source: SRC-GLB001 (Enderton Ch. 0), SRC-BST001 (Halmos Ch. 11)
  - Referenced by: SYN (arity, formula complexity), SEM (cardinality comparisons), DED (proof length, induction on derivations), CMP (domain of computable functions), SET (formal $\omega$)
  - Fragment: both
  - Motivating example: The arity of a relation symbol $R$ is a natural number $n \in \mathbb{N}$. The length of a derivation is a natural number.

- PRIM-BST013: **Mathematical Induction**
  - Description: The principle that to prove a property $P$ holds for all natural numbers, it suffices to prove: (i) $P(0)$ holds (base case), and (ii) for all $n$, if $P(n)$ holds then $P(n+1)$ holds (inductive step). This is the engine of most metatheoretic proofs.
  - Formal: $[P(0) \land \forall n\,(P(n) \to P(n+1))] \to \forall n\, P(n)$.
  - Ownership: OWNS
  - Source: SRC-GLB001 (Enderton Ch. 0), SRC-BST001 (Halmos Ch. 11)
  - Referenced by: SYN (structural induction on formulas is a generalization), SEM (induction on satisfaction definition), DED (induction on proof length for soundness), CMP (induction on computation steps)
  - Fragment: both
  - Motivating example: To prove that every formula has equal numbers of left and right parentheses, prove it for atomic formulas (base) and show each formation rule preserves the property (inductive step).

- PRIM-BST014: **Inductive Definition**
  - Description: A method of defining a set (or function) by specifying base elements and closure rules. The defined set is the smallest set satisfying the base and closure conditions. This is the standard method for defining the set of terms, the set of formulas, and derivation trees in logic.
  - Formal: Given base set $B$ and closure operations $f_1, \ldots, f_k$, the inductively defined set $I$ is the intersection of all sets containing $B$ and closed under $f_1, \ldots, f_k$: $I = \bigcap \{X : B \subseteq X \land \forall i\,(f_i[X] \subseteq X)\}$.
  - Ownership: OWNS
  - Source: SRC-GLB001 (Enderton Ch. 1), SRC-GLB002 (Shoenfield Ch. 2)
  - Referenced by: SYN (inductive definition of terms and formulas), SEM (recursive definition of satisfaction), DED (inductive definition of derivations), CMP (recursive function definitions)
  - Fragment: both
  - Motivating example: The set of propositional formulas is inductively defined: (base) every propositional variable is a formula; (closure) if $\varphi$ and $\psi$ are formulas, then $(\neg \varphi)$, $(\varphi \to \psi)$, $(\varphi \land \psi)$, $(\varphi \lor \psi)$ are formulas.

- PRIM-BST015: **Power Set (naive) ($\mathcal{P}(A)$)**
  - Description: The collection of all subsets of a given set $A$. At Level-0, we assume this collection exists as a set without formal justification. Formal justification is provided by AX-SET004 (Power Set Axiom) in DOMAIN-SET-FORMAL.md.
  - Formal: $\mathcal{P}(A) = \{X : X \subseteq A\}$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 5)
  - Referenced by: SEM (set of all truth-value assignments $\{0,1\}^{\text{PropVar}}$ is related to $\mathcal{P}$), SET (formal Power Set axiom)
  - Fragment: both
  - Motivating example: $\mathcal{P}(\{a, b\}) = \{\emptyset, \{a\}, \{b\}, \{a, b\}\}$. The set of all truth-value assignments on $n$ propositional variables has $2^n$ elements.

- PRIM-BST016: **Cardinality (Finite, Countable, Uncountable)**
  - Description: Two sets have the same cardinality if there exists a bijection between them. A set is finite if it is in bijection with $\{1, \ldots, n\}$ for some $n \in \mathbb{N}$. A set is countably infinite if it is in bijection with $\mathbb{N}$. A set is countable if it is finite or countably infinite. A set is uncountable if it is not countable.
  - Formal: $|A| = |B| \iff \exists f : A \xrightarrow{\sim} B$ (bijection). Finite: $|A| = n$ for some $n \in \mathbb{N}$. Countable: $|A| \leq |\mathbb{N}|$. Uncountable: $|A| > |\mathbb{N}|$.
  - Ownership: OWNS
  - Source: SRC-BST001 (Halmos Ch. 13), SRC-GLB001 (Enderton Ch. 0)
  - Referenced by: SEM (countable/uncountable models, Lowenheim-Skolem), CMP (countability of programs, uncountability of functions), SET (formal cardinal arithmetic)
  - Fragment: FOL (PL works entirely within finite sets)
  - Motivating example: $\mathbb{N}$ is countably infinite. $\mathbb{R}$ is uncountable (Cantor's diagonal argument). The set of all formulas in a countable language is countable. The set of all subsets of $\mathbb{N}$ is uncountable.

## 4. Axioms

BST has no axioms. This is by design: Level-0 operates as naive, unaxiomatized mathematical background. The concepts above are taken as understood, not postulated. Formal axiomatization of set-theoretic concepts is the province of SET (DOMAIN-SET-FORMAL.md).

## 5. Definitions (Conservative Extensions)

- DEF-BST001: **Injection (One-to-One Function)**
  - Definition: A function $f : A \to B$ is injective if $f(a_1) = f(a_2)$ implies $a_1 = a_2$ for all $a_1, a_2 \in A$.
  - Depends: PRIM-BST009 (function)
  - Ownership: OWNS
  - Referenced by: SEM (isomorphism requires bijection), CMP (encoding functions), SET (cardinality comparison)
  - Fragment: both
  - Motivating example: $f : \mathbb{N} \to \mathbb{N}$ defined by $f(n) = 2n$ is injective. The Godel numbering function is injective (distinct expressions receive distinct codes).

- DEF-BST002: **Surjection (Onto Function)**
  - Definition: A function $f : A \to B$ is surjective if for every $b \in B$ there exists $a \in A$ with $f(a) = b$.
  - Depends: PRIM-BST009 (function)
  - Ownership: OWNS
  - Referenced by: SEM (surjective homomorphisms), CMP (enumeration functions)
  - Fragment: both
  - Motivating example: $f : \mathbb{Z} \to \mathbb{N}$ defined by $f(n) = |n|$ is surjective but not injective.

- DEF-BST003: **Bijection (One-to-One Correspondence)**
  - Definition: A function that is both injective and surjective. Bijections establish "same size" between sets.
  - Depends: DEF-BST001 (injection), DEF-BST002 (surjection)
  - Ownership: OWNS
  - Referenced by: SEM (isomorphism of structures), CMP (Godel numbering as encoding), SET (equinumerosity)
  - Fragment: both
  - Motivating example: $f : \mathbb{N} \to \mathbb{Z}$ defined by $f(2k) = k$, $f(2k+1) = -(k+1)$ is a bijection, showing $|\mathbb{N}| = |\mathbb{Z}|$.

- DEF-BST004: **Equivalence Relation**
  - Definition: A binary relation $\sim$ on a set $A$ that is reflexive ($a \sim a$), symmetric ($a \sim b \implies b \sim a$), and transitive ($a \sim b \land b \sim c \implies a \sim c$).
  - Depends: PRIM-BST008 (relation)
  - Ownership: OWNS
  - Referenced by: SEM (elementary equivalence, isomorphism), SYN (alphabetic variants)
  - Fragment: both
  - Motivating example: Logical equivalence of formulas: $\varphi \equiv \psi$ iff $\varphi$ and $\psi$ have the same truth value under every interpretation. This is reflexive, symmetric, and transitive.

- DEF-BST005: **Partial Order**
  - Definition: A binary relation $\leq$ on a set $A$ that is reflexive, antisymmetric ($a \leq b \land b \leq a \implies a = b$), and transitive.
  - Depends: PRIM-BST008 (relation)
  - Ownership: OWNS
  - Referenced by: SET (well-ordering, ordinals), SEM (substructure ordering)
  - Fragment: both
  - Motivating example: $\subseteq$ on $\mathcal{P}(A)$ is a partial order. The set of subformulas of a formula, ordered by the subformula relation, forms a partial order.

## 6. Key Theorems

- THM-BST001: **Cantor's Theorem (Naive)**
  - Statement: For any set $A$, there is no surjection from $A$ onto $\mathcal{P}(A)$. Equivalently, $|A| < |\mathcal{P}(A)|$.
  - Depends: PRIM-BST015 (power set), DEF-BST002 (surjection), PRIM-BST016 (cardinality)
  - Proof sketch: Suppose $f : A \to \mathcal{P}(A)$ is surjective. Consider $D = \{a \in A : a \notin f(a)\}$. Since $f$ is surjective, $D = f(d)$ for some $d$. Then $d \in D \iff d \notin f(d) = D$, contradiction. (Diagonal argument.)
  - Source: SRC-BST001 (Halmos Ch. 25)

- THM-BST002: **$\mathbb{N}$ is Countably Infinite**
  - Statement: $\mathbb{N}$ is infinite and every infinite subset of $\mathbb{N}$ is countably infinite.
  - Depends: PRIM-BST012 ($\mathbb{N}$), PRIM-BST016 (cardinality)
  - Proof sketch: $\mathbb{N}$ is infinite because the successor function $n \mapsto n+1$ is an injection from $\mathbb{N}$ to a proper subset. Every infinite subset can be enumerated by listing its elements in increasing order.

- THM-BST003: **Countable Union of Countable Sets is Countable**
  - Statement: If $A_0, A_1, A_2, \ldots$ are countable sets, then $\bigcup_{i \in \mathbb{N}} A_i$ is countable.
  - Depends: PRIM-BST012 ($\mathbb{N}$), PRIM-BST016 (cardinality), PRIM-BST005 (union)
  - Proof sketch: Dovetailing / diagonal enumeration. Enumerate elements of $A_0, A_1, \ldots$ in a grid and traverse diagonally, skipping duplicates.

## 7. Invariants & Constraints

- INV-BST001: **Extensionality**
  - Statement: Sets are determined by their members: $A = B \iff \forall x\,(x \in A \leftrightarrow x \in B)$.
  - Justification: This is the fundamental identity criterion for sets at Level-0. It ensures that "set" is a well-defined notion — there are no two different sets with exactly the same members.

- INV-BST002: **Level-0 Only**
  - Statement: BST concepts are metalanguage tools. They MUST NOT be confused with object-language concepts from SET, SYN, SEM, or DED.
  - Justification: The metatheory stratification (CONVENTIONS.md Section 2) requires maintaining the Level-0/Level-1 distinction. A BST "function" is a metalanguage mapping; a SYN "function symbol" is a formal symbol in an object language.

- FORBID-BST001: **No Axiomatization**
  - Statement: BST MUST NOT include axiom entries. Any axiomatic constraint on sets belongs to SET.
  - Consequence: If BST included axioms, it would collapse the Level-0/Level-1 distinction and create circularity (the metalanguage would need its own formal system, which would need its own metalanguage, etc.).

## 8. Extension Points

- EXT-BST001: **Transfinite Concepts**
  - Fixed: Finite and countable cardinality (PRIM-BST016). Natural number induction (PRIM-BST013).
  - Parameterizable: Extension to ordinals, cardinals, transfinite induction, transfinite recursion.
  - Extension type: Additive
  - Examples: SET adds formal ordinals and cardinals. Advanced model theory may require uncountable cardinals for Lowenheim-Skolem.

- EXT-BST002: **Accessibility Relations (for Modal Logic)**
  - Fixed: Binary relation (PRIM-BST008).
  - Parameterizable: Special types of relations (reflexive, transitive, symmetric, Euclidean, serial) used as accessibility relations in Kripke semantics.
  - Extension type: Additive
  - Examples: Modal logic extensions add specific relation properties to model different modal systems (T: reflexive, S4: reflexive+transitive, S5: equivalence relation).

## 9. Intra-Domain Dependency Graph

```
PRIM-BST001 (Set) ---- PRIM-BST002 (Membership)
     |                       |
     v                       v
PRIM-BST003 (Subset)   PRIM-BST004 (Empty Set)
     |
     v
PRIM-BST005 (Union/Intersection)
     |
     v
PRIM-BST006 (Ordered Pair)
     |
     v
PRIM-BST007 (Cartesian Product)
     |
     +------> PRIM-BST008 (Relation)
     |              |
     v              v
PRIM-BST009 (Function)
     |
     +------> PRIM-BST010 (Finite Sequence)
     |
     +------> PRIM-BST011 (Infinite Sequence)
     |
     v
PRIM-BST012 (Natural Number)
     |
     +------> PRIM-BST013 (Mathematical Induction)
     |
     +------> PRIM-BST014 (Inductive Definition)
     |
     v
PRIM-BST015 (Power Set)
     |
     v
PRIM-BST016 (Cardinality)
     |
     v
DEF-BST001 (Injection) ---> DEF-BST003 (Bijection)
DEF-BST002 (Surjection) --> DEF-BST003 (Bijection)
DEF-BST004 (Equivalence Relation) [depends: PRIM-BST008]
DEF-BST005 (Partial Order) [depends: PRIM-BST008]
```

## 10. Cross-Domain Interface

### Exports

| ID | Concept | Consumed by |
|----|---------|-------------|
| PRIM-BST001 | Set | SYN, SEM, DED, CMP, SET |
| PRIM-BST002 | Membership | SYN, SEM, DED, CMP, SET |
| PRIM-BST003 | Subset | SEM, SET |
| PRIM-BST004 | Empty Set | SEM, DED, SET |
| PRIM-BST005 | Union/Intersection | SYN, SEM, DED |
| PRIM-BST006 | Ordered Pair | SEM, DED, CMP |
| PRIM-BST007 | Cartesian Product | SEM, DED, CMP |
| PRIM-BST008 | Relation | SYN, SEM, CMP |
| PRIM-BST009 | Function | SYN, SEM, DED, CMP |
| PRIM-BST010 | Finite Sequence | SYN, DED, CMP |
| PRIM-BST011 | Infinite Sequence | SEM, CMP |
| PRIM-BST012 | Natural Number | SYN, SEM, DED, CMP, SET |
| PRIM-BST013 | Mathematical Induction | SYN, SEM, DED, CMP |
| PRIM-BST014 | Inductive Definition | SYN, SEM, DED, CMP |
| PRIM-BST015 | Power Set (naive) | SEM, SET |
| PRIM-BST016 | Cardinality | SEM, CMP, SET |
| DEF-BST001 | Injection | SEM, CMP, SET |
| DEF-BST002 | Surjection | SEM, CMP |
| DEF-BST003 | Bijection | SEM, CMP, SET |
| DEF-BST004 | Equivalence Relation | SEM, SYN |
| DEF-BST005 | Partial Order | SET, SEM |

### Imports

None. BST is the root.

## 11. Completeness Argument

**Why these primitives cover the domain**: The 16 primitives and 5 definitions provide the complete naive set-theoretic toolkit used in the metalanguage of standard logic textbooks. Specifically:

- **SYN needs**: sets (of symbols, of formulas), sequences (strings), functions (arity), inductive definitions (formation rules), natural numbers (formula complexity). All provided by PRIM-BST001, 009, 010, 012, 014.
- **SEM needs**: sets (domains), functions (interpretations, assignments), relations (structure components), Cartesian products (n-ary relations), sequences (variable assignments), cardinality (model sizes), power sets (truth-value assignment spaces). All provided.
- **DED needs**: sets (of assumptions), sequences (derivations), functions (rule applications), natural numbers (proof length), induction (proof by induction on derivation length). All provided.
- **CMP needs**: natural numbers (domain of computable functions), functions (computable functions), sequences (computation traces), cardinality (countable vs. uncountable), sets (decidable sets). All provided.

**Evidence of a gap**: If any domain spec requires a naive set-theoretic concept not listed here (e.g., a specific type of ordering, a combinatorial principle), that concept should be added to BST or shown to be definable from existing BST entries.

**OL chapters**: `content/sets-functions-relations/` maps directly to BST.

## 12. OpenLogic Mapping

| OL Chapter/Section | Maps to |
|---|---|
| `content/sets-functions-relations/sets/` | PRIM-BST001, PRIM-BST002, PRIM-BST003, PRIM-BST004, PRIM-BST005 |
| `content/sets-functions-relations/relations/` | PRIM-BST006, PRIM-BST007, PRIM-BST008, DEF-BST004, DEF-BST005 |
| `content/sets-functions-relations/functions/` | PRIM-BST009, DEF-BST001, DEF-BST002, DEF-BST003 |
| `content/sets-functions-relations/size-of-sets/` | PRIM-BST016, THM-BST001, THM-BST002, THM-BST003 |
| `content/methods/induction/` | PRIM-BST013, PRIM-BST014 |

## 13. Self-Audit Checklist

- [x] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [x] Every THM depends only on previously listed AX/DEF/THM
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports (N/A — BST imports nothing)
- [x] Dissolution argument is present and non-trivial
- [x] Extension points cover applicable types (additive for BST; replacement/structural N/A)
- [x] Intra-domain dependency graph is acyclic
- [x] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [x] Motivating examples are present for all PRIM and key DEF entries
- [x] No PRIM/DEF duplicates an entry in another domain (BST is first; checked against empty registry)
- [x] Completeness argument addresses all relevant OL chapters
