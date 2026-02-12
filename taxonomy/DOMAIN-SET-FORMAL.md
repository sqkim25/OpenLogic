# DOMAIN-SET-FORMAL v0.1

## 0. Sources & Assumptions

- SRC-SET001: Kunen, *Set Theory: An Introduction to Independence Proofs*, 1980
- SRC-SET002: Jech, *Set Theory*, 3rd millennium ed., 2003
- SRC-SET003: Enderton, *Elements of Set Theory*, 1977
- ASM-SET001: We present ZFC (Zermelo-Fraenkel with Choice) as the standard axiomatic set theory. Justification: ZFC is the standard foundational theory for mathematics, used by all major logic textbooks. Alternative set theories (NBG, MK, ZF without choice) are noted but not developed.
- ASM-SET002: We scope set theory to "for logic": ZFC axioms, ordinals and cardinals for model theory and metatheorems, basic transfinite recursion. Justification: ASM-GLB005.
- UNK-SET001: Should the von Neumann hierarchy ($V_\alpha$) be included? Resolution: included as a deferred definition (DEF-SET012) — needed for CP-003 (compactness via ultraproducts uses cardinality arguments) and model theory supplement. Resolved.

## 1. Domain Intent

- **Irreducible question**: What is the formal mathematical universe?
- **Scope**: ZFC as a specific first-order theory in the language $\mathcal{L}_\in = \{\in\}$. The 9 ZFC axioms, ordinal and cardinal numbers as formal objects, transfinite induction and recursion, and the key equivalences (AC $\iff$ well-ordering $\iff$ Zorn's lemma). This is Level-1 set theory — a formal object of study, analyzed using the SYN/SEM/DED/BST apparatus.
- **Non-goals**: Forcing and independence results (too specialized). Large cardinals (beyond the scope of "set theory for logic"). Descriptive set theory. Inner models (constructibility, $L$). Naive set-theoretic metalanguage (that is BST).
- **Dissolution argument**: Set membership ($\in$) and the ZFC axioms form the formal foundation for virtually all of mathematics. The cumulative hierarchy, ordinals, and cardinals provide the raw material from which structures, domains, and functions used by other domains are built. SET cannot be merged into BST because BST is naive/un-axiomatized while SET is a specific first-order theory amenable to metatheoretic analysis. SET cannot be merged into SEM because SET is a *theory* with semantics, not semantics itself — it is a subject of study using the tools of SEM, not a tool of study. A "model of ZFC" is a structure in the sense of SEM, but the axioms of ZFC are sentences analyzed by DED.

## 2. Prerequisites

- DEP-SET001: Requires SYN for PRIM-SYN009 (language — $\mathcal{L}_\in$ is a specific first-order language), PRIM-SYN012 (formula), PRIM-SYN013 (sentence), PRIM-SYN018 (equality symbol)
- DEP-SET002: Requires SEM for PRIM-SEM001 (structure — models of ZFC are $\mathcal{L}_\in$-structures), PRIM-SEM011 (model)
- DEP-SET003: Requires DED for PRIM-DED006 (provability — proofs within ZFC), PRIM-DED002 (non-logical axiom)
- DEP-SET004: Requires BST for PRIM-BST001 (set — naive sets for the metalanguage), PRIM-BST009 (function), PRIM-BST012 (natural number), PRIM-BST013 (induction)

## 3. Primitive Notions

- PRIM-SET001: **Set (Formal)**
  - Description: In ZFC, a set is any object in the domain of a model of ZFC. Unlike BST's naive sets (Level-0), formal sets are governed by the ZFC axioms — they exist only to the extent that the axioms guarantee their existence. This is a Level-1 concept: sets as objects within a formal first-order theory.
  - Formal: The variables of $\mathcal{L}_\in$ range over sets. The axioms specify which sets exist and how they relate via $\in$.
  - Ownership: OWNS (distinct from PRIM-BST001 — BST's set is naive/metalanguage, SET's set is formal/axiomatized. Boundary: P5)
  - Source: SRC-GLB010 (Zermelo 1908), SRC-SET001 (Kunen Ch. 1)
  - Referenced by: SEM (models of ZFC consist of formal sets), CMP (arithmetic within set theory)
  - Fragment: FOL
  - Motivating example: In ZFC, $\emptyset$ exists (by Separation from any set). $\{a, b\}$ exists (by Pairing). $\mathcal{P}(\omega)$ exists (by Power Set + Infinity). But "the set of all sets" does NOT exist (Russell's paradox — prevented by the axiom of Foundation and the absence of unrestricted comprehension).

- PRIM-SET002: **Membership ($\in$, formal)**
  - Description: The sole non-logical symbol of $\mathcal{L}_\in$, a binary relation symbol. "$x \in y$" is the fundamental atomic formula of set theory. All set-theoretic concepts (subset, union, power set, ordinal, cardinal, function, etc.) are defined in terms of $\in$ and logical connectives/quantifiers.
  - Formal: $\in$ is a binary relation symbol: $\mathcal{L}_\in = \{\in\}$, $\text{ar}(\in) = 2$. $(x \in y)$ is an atomic formula.
  - Ownership: OWNS (distinct from PRIM-BST002 — BST's membership is naive, SET's is the formal relation symbol of $\mathcal{L}_\in$. Boundary: P5)
  - Source: SRC-GLB010 (Zermelo 1908), SRC-SET001 (Kunen Ch. 1)
  - Referenced by: SYN (as a relation symbol in $\mathcal{L}_\in$), SEM (interpreted in models of ZFC)
  - Fragment: FOL
  - Motivating example: $\emptyset \in \{\emptyset\}$ is a true sentence of ZFC. $\emptyset \in \emptyset$ is a false sentence. $x \in x$ is ruled out (for well-founded sets) by the Axiom of Foundation.

- PRIM-SET003: **Class (Informal)**
  - Description: A "collection" defined by a formula $\varphi(x)$ — the "class of all $x$ such that $\varphi(x)$." A class that is a set (i.e., is a member of some other set) is called a "small class" or just a "set." A class that is NOT a set is a "proper class." Proper classes arise naturally (the class of all sets, the class of all ordinals) but are not objects within ZFC — they are metatheoretic shorthand.
  - Formal: $\{x : \varphi(x)\}$ denotes the class of all sets satisfying $\varphi$. If there exists a set $A$ with $A = \{x : \varphi(x)\}$, the class is a set. Otherwise it is a proper class. ZFC does not formally quantify over classes; class notation is a metalanguage convenience.
  - Ownership: OWNS
  - Source: SRC-SET001 (Kunen Ch. 1), SRC-SET002 (Jech Ch. 1)
  - Referenced by: (internal — proper classes are used informally throughout set theory)
  - Fragment: FOL
  - Motivating example: $V = \{x : x = x\}$ (the class of all sets) is a proper class. $\text{Ord} = \{x : x \text{ is an ordinal}\}$ is a proper class. $\omega = \{0, 1, 2, \ldots\}$ is a set (exists by the Axiom of Infinity).

## 4. Axioms

All axioms are sentences (or schemas) in $\mathcal{L}_\in$. They are non-logical axioms (PRIM-DED002) of the specific theory ZFC.

- AX-SET001: **Extensionality**
  - Statement: $\forall x\, \forall y\, [\forall z\, (z \in x \leftrightarrow z \in y) \to x = y]$
  - Depends: PRIM-SET002 ($\in$), PRIM-SYN018 ($=$)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: Two sets are equal if and only if they have exactly the same members. Sets are determined entirely by their elements.

- AX-SET002: **Pairing**
  - Statement: $\forall x\, \forall y\, \exists z\, \forall w\, (w \in z \leftrightarrow w = x \lor w = y)$
  - Depends: PRIM-SET002 ($\in$)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: For any two sets $x$ and $y$, the set $\{x, y\}$ exists. Combined with extensionality, this also gives singletons $\{x\} = \{x, x\}$.

- AX-SET003: **Union**
  - Statement: $\forall x\, \exists y\, \forall z\, (z \in y \leftrightarrow \exists w\, (z \in w \land w \in x))$
  - Depends: PRIM-SET002 ($\in$)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: For any set $x$, the union $\bigcup x = \{z : \exists w \in x\, (z \in w)\}$ exists. This "flattens" a set of sets into a single set.

- AX-SET004: **Power Set**
  - Statement: $\forall x\, \exists y\, \forall z\, (z \in y \leftrightarrow z \subseteq x)$, where $z \subseteq x$ abbreviates $\forall w\, (w \in z \to w \in x)$.
  - Depends: PRIM-SET002 ($\in$)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: For any set $x$, the set of all subsets of $x$ (the power set $\mathcal{P}(x)$) exists. This is the formal justification for BST's naive use of power sets (PRIM-BST015).

- AX-SET005: **Infinity**
  - Statement: $\exists x\, [\emptyset \in x \land \forall y\, (y \in x \to y \cup \{y\} \in x)]$
  - Depends: PRIM-SET002 ($\in$), AX-SET002 (Pairing), AX-SET003 (Union)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: There exists an infinite set — specifically, a set containing $\emptyset$, $\{\emptyset\}$, $\{\emptyset, \{\emptyset\}\}$, etc. (the von Neumann natural numbers). This axiom guarantees the existence of $\omega$, the set of natural numbers.

- AX-SET006: **Separation (Comprehension Schema)**
  - Statement: For each formula $\varphi(x, \bar{p})$ (with parameters $\bar{p}$): $\forall \bar{p}\, \forall A\, \exists B\, \forall x\, (x \in B \leftrightarrow x \in A \land \varphi(x, \bar{p}))$.
  - Depends: PRIM-SET002 ($\in$), PRIM-SYN012 (formula — this is an axiom schema, one axiom for each formula $\varphi$)
  - Source: SRC-GLB010 (Zermelo 1908)
  - Normative: MUST
  - Natural language: Given any set $A$ and any property expressible in $\mathcal{L}_\in$, the subset of $A$ consisting of elements satisfying that property exists. This is RESTRICTED comprehension — you can only "separate out" a subset of an existing set. Unrestricted comprehension ($\{x : \varphi(x)\}$ without bounding set) leads to Russell's paradox.

- AX-SET007: **Replacement (Schema)**
  - Statement: For each formula $\varphi(x, y, \bar{p})$: if $\forall x \in A\, \exists! y\, \varphi(x, y, \bar{p})$ (i.e., $\varphi$ defines a function on $A$), then $\{y : \exists x \in A\, \varphi(x, y, \bar{p})\}$ exists as a set.
  - Depends: PRIM-SET002 ($\in$), PRIM-SYN012 (formula — axiom schema)
  - Source: Fraenkel (1922), Skolem (1922)
  - Normative: MUST
  - Natural language: The image of a set under a definable function is a set. If you can define a function (via a formula) on a set $A$, the range of that function is also a set.

- AX-SET008: **Foundation (Regularity)**
  - Statement: $\forall x\, [x \neq \emptyset \to \exists y\, (y \in x \land y \cap x = \emptyset)]$
  - Depends: PRIM-SET002 ($\in$)
  - Source: von Neumann (1925), Zermelo (1930)
  - Normative: MUST
  - Natural language: Every non-empty set has an $\in$-minimal element. This prevents pathological sets like $x \in x$ or infinite descending $\in$-chains $\ldots \in x_2 \in x_1 \in x_0$. It ensures sets are "well-founded."

- AX-SET009: **Choice (AC)**
  - Statement: For every set $A$ of non-empty sets, there exists a choice function $f : A \to \bigcup A$ such that $f(x) \in x$ for every $x \in A$.
  - Depends: PRIM-SET002 ($\in$), PRIM-BST009 (function — the choice function is a metalevel function, but AC asserts the existence of a corresponding set-theoretic function)
  - Source: Zermelo (1904)
  - Normative: MUST (for ZFC; ZF = ZFC minus Choice)
  - Natural language: Given any collection of non-empty sets, you can "choose" one element from each. This is non-constructive — AC asserts existence without providing a method. AC is independent of ZF (Godel showed ZF + AC is consistent if ZF is; Cohen showed ZF + $\neg$AC is consistent if ZF is).

## 5. Definitions (Conservative Extensions)

### Core Definitions

- DEF-SET001: **Ordinal Number (von Neumann)**
  - Definition: A set $\alpha$ is an ordinal if it is transitive ($\forall x \in \alpha\, (x \subseteq \alpha)$) and well-ordered by $\in$. The ordinals extend the natural numbers through the transfinite: $0 = \emptyset$, $1 = \{\emptyset\}$, $2 = \{\emptyset, \{\emptyset\}\}$, $\ldots$, $\omega = \{0, 1, 2, \ldots\}$, $\omega + 1 = \omega \cup \{\omega\}$, $\ldots$
  - Depends: PRIM-SET001 (set), PRIM-SET002 ($\in$), AX-SET008 (Foundation ensures well-ordering)
  - Ownership: OWNS
  - Referenced by: SEM (ordinals used in Lowenheim-Skolem, ordinal-indexed constructions)
  - Fragment: FOL
  - Motivating example: $0 = \emptyset$, $1 = \{0\}$, $2 = \{0, 1\}$, $\omega = \{0, 1, 2, \ldots\}$, $\omega + 1 = \{0, 1, 2, \ldots, \omega\}$.

- DEF-SET002: **Successor Ordinal**
  - Definition: An ordinal of the form $\alpha + 1 = \alpha \cup \{\alpha\}$. Successor ordinals are the "next" ordinal after a given one.
  - Depends: DEF-SET001 (ordinal), AX-SET002 (Pairing), AX-SET003 (Union)
  - Ownership: OWNS
  - Referenced by: (internal)
  - Fragment: FOL
  - Motivating example: $1 = 0 + 1 = \{0\}$. $\omega + 1 = \omega \cup \{\omega\}$.

- DEF-SET003: **Limit Ordinal**
  - Definition: A non-zero ordinal that is not a successor ordinal. Equivalently, $\lambda$ is a limit ordinal iff $\lambda = \bigcup \lambda$ (it is the supremum of all smaller ordinals). The first limit ordinal is $\omega$.
  - Depends: DEF-SET001 (ordinal), DEF-SET002 (successor ordinal)
  - Ownership: OWNS
  - Referenced by: (internal — limit ordinals drive transfinite recursion)
  - Fragment: FOL
  - Motivating example: $\omega$ is a limit ordinal (it is $\sup\{0, 1, 2, \ldots\}$, not a successor). $\omega + \omega = \omega \cdot 2$ is also a limit ordinal.

- DEF-SET004: **$\omega$ (The Set of Natural Numbers)**
  - Definition: The smallest limit ordinal, guaranteed to exist by AX-SET005 (Infinity). $\omega = \{0, 1, 2, 3, \ldots\}$ under the von Neumann encoding. This is the formal counterpart of BST's $\mathbb{N}$ (PRIM-BST012).
  - Depends: DEF-SET001 (ordinal), DEF-SET003 (limit ordinal), AX-SET005 (Infinity)
  - Ownership: OWNS (formal $\omega$; BST owns naive $\mathbb{N}$. Boundary: P5)
  - Referenced by: SEM (standard model of arithmetic has domain $\omega$), CMP ($\omega$ as the formal domain for computable functions)
  - Fragment: FOL
  - Motivating example: $\omega \vDash$ PA (the set $\omega$ with the standard interpretation of successor, addition, multiplication is a model of the Peano axioms).

- DEF-SET005: **Transfinite Induction**
  - Definition: The principle that if a property $P$ holds for $\emptyset$, and holding for all $\beta < \alpha$ implies holding for $\alpha$, then $P$ holds for all ordinals. This extends PRIM-BST013 (mathematical induction) beyond $\omega$.
  - Formal: $[\forall \alpha\, ((\forall \beta < \alpha\, P(\beta)) \to P(\alpha))] \to \forall \alpha\, P(\alpha)$.
  - Depends: DEF-SET001 (ordinal), AX-SET008 (Foundation — ensures $\in$ is well-founded on ordinals)
  - Ownership: OWNS
  - Referenced by: SEM (transfinite constructions in model theory)
  - Fragment: FOL
  - Motivating example: To prove every ordinal has a unique Cantor normal form, use transfinite induction: base case ($0$), successor case, limit case.

- DEF-SET006: **Transfinite Recursion**
  - Definition: The principle that allows defining a function $F$ on all ordinals by specifying: $F(0)$, $F(\alpha + 1)$ in terms of $F(\alpha)$, and $F(\lambda)$ in terms of $\{F(\beta) : \beta < \lambda\}$ for limit $\lambda$.
  - Formal: Given $G$ (specifying how to compute the next value), there exists a unique function $F : \text{Ord} \to V$ such that $F(\alpha) = G(F \upharpoonright \alpha)$ for all $\alpha$.
  - Depends: DEF-SET005 (transfinite induction), AX-SET007 (Replacement — ensures the function values form sets)
  - Ownership: OWNS
  - Referenced by: SEM (building chains of structures), DED (ordinal analysis of proof theory)
  - Fragment: FOL
  - Motivating example: The von Neumann hierarchy: $V_0 = \emptyset$, $V_{\alpha+1} = \mathcal{P}(V_\alpha)$, $V_\lambda = \bigcup_{\beta < \lambda} V_\beta$. This is defined by transfinite recursion.

- DEF-SET007: **Cardinal Number**
  - Definition: The cardinality (size) of a set, formalized using ordinals. The cardinal $|A|$ is the least ordinal equinumerous with $A$ (using AC, every set can be well-ordered, hence equinumerous with some ordinal). Infinite cardinals are denoted $\aleph_0, \aleph_1, \ldots$
  - Formal: $|A| = $ the least ordinal $\alpha$ such that there exists a bijection $f : A \to \alpha$. $\aleph_0 = \omega$. $\aleph_{\alpha+1} = $ the least cardinal $> \aleph_\alpha$.
  - Depends: DEF-SET001 (ordinal), DEF-BST003 (bijection), AX-SET009 (Choice)
  - Ownership: OWNS (formal cardinals; BST owns naive cardinality PRIM-BST016. Boundary: P5)
  - Referenced by: SEM (model sizes in Lowenheim-Skolem)
  - Fragment: FOL
  - Motivating example: $|\mathbb{N}| = \aleph_0$. $|\mathbb{R}| = 2^{\aleph_0}$. Whether $2^{\aleph_0} = \aleph_1$ (the Continuum Hypothesis) is independent of ZFC.

- DEF-SET008: **Cardinality ($|A|$, Formal)**
  - Definition: The cardinal number of a set $A$ — the unique cardinal equinumerous with $A$.
  - Formal: $|A|$ as in DEF-SET007.
  - Depends: DEF-SET007 (cardinal number), DEF-BST003 (bijection)
  - Ownership: OWNS
  - Referenced by: SEM (sizes of models and domains)
  - Fragment: FOL
  - Motivating example: $|\omega| = \aleph_0$. $|\mathcal{P}(\omega)| = 2^{\aleph_0}$.

- DEF-SET009: **Well-Ordering**
  - Definition: A total order $\leq$ on a set $A$ such that every non-empty subset of $A$ has a least element. Well-orderings are the backbone of transfinite induction.
  - Formal: $(A, \leq)$ is a well-ordering iff $\leq$ is a total order on $A$ and every non-empty $B \subseteq A$ has a $\leq$-least element.
  - Depends: PRIM-BST008 (relation), DEF-BST005 (partial order)
  - Ownership: OWNS
  - Referenced by: SEM (well-ordered domains, ordinal structures)
  - Fragment: FOL
  - Motivating example: $(\mathbb{N}, \leq)$ is a well-ordering. $(\mathbb{Z}, \leq)$ is NOT a well-ordering (no least element). Every ordinal with $\in$ is a well-ordering.

- DEF-SET010: **Zorn's Lemma**
  - Definition: If every chain (totally ordered subset) in a partially ordered set $P$ has an upper bound in $P$, then $P$ has a maximal element. Equivalent to AC and the well-ordering theorem.
  - Formal: If $(P, \leq)$ is a partial order and every chain $C \subseteq P$ has an upper bound in $P$, then $P$ has a maximal element $m$ (no $p \in P$ with $p > m$).
  - Depends: DEF-BST005 (partial order), AX-SET009 (Choice — Zorn's lemma is equivalent to AC)
  - Ownership: OWNS
  - Referenced by: DED (Lindenbaum's lemma uses Zorn's lemma), SEM (existence of maximal consistent extensions)
  - Fragment: FOL
  - Motivating example: Every vector space has a basis (apply Zorn's lemma to the partial order of linearly independent subsets). In logic: every consistent theory extends to a maximal consistent theory (Lindenbaum's lemma).

- DEF-SET011: **Cantor's Theorem (Formal)**
  - Definition: For any set $A$, $|A| < |\mathcal{P}(A)|$. There is no surjection from $A$ onto $\mathcal{P}(A)$.
  - Formal: $\forall A\, \neg \exists f\, (f : A \twoheadrightarrow \mathcal{P}(A))$.
  - Depends: AX-SET004 (Power Set), DEF-SET008 (cardinality), DEF-BST002 (surjection)
  - Ownership: OWNS (formal version within ZFC; THM-BST001 is the naive version)
  - Referenced by: SEM (cardinality arguments in model theory)
  - Fragment: FOL
  - Motivating example: $|\omega| = \aleph_0 < 2^{\aleph_0} = |\mathcal{P}(\omega)|$. The proof is the same diagonal argument as THM-BST001 but now justified within ZFC.

### Deferred Definitions

*Include if needed by specific composition patterns or SEM supplement.*

- DEF-SET012: **Von Neumann Hierarchy ($V_\alpha$)** [Deferred]
  - Definition: $V_0 = \emptyset$, $V_{\alpha+1} = \mathcal{P}(V_\alpha)$, $V_\lambda = \bigcup_{\beta < \lambda} V_\beta$ for limit $\lambda$. $V = \bigcup_\alpha V_\alpha$ is the cumulative hierarchy — every set belongs to some $V_\alpha$.
  - Depends: DEF-SET006 (transfinite recursion), AX-SET004 (Power Set), AX-SET008 (Foundation)
  - Ownership: OWNS
  - Referenced by: SEM (rank of sets, absoluteness arguments)
  - Fragment: FOL
  - Condition for inclusion: needed if CP-003 or SEM supplement requires rank arguments.

- DEF-SET013: **$\aleph$ Numbers** [Deferred]
  - Definition: $\aleph_0 = \omega$, $\aleph_{\alpha+1} = $ the least cardinal $> \aleph_\alpha$, $\aleph_\lambda = \sup_{\beta < \lambda} \aleph_\beta$ for limit $\lambda$.
  - Depends: DEF-SET007 (cardinal), DEF-SET006 (transfinite recursion)
  - Ownership: OWNS
  - Fragment: FOL
  - Condition for inclusion: needed for advanced cardinality arguments in model theory.

- DEF-SET014: **Cofinality** [Deferred]
  - Definition: The cofinality $\text{cf}(\alpha)$ of a limit ordinal $\alpha$ is the smallest ordinal $\beta$ such that there is a cofinal function $f : \beta \to \alpha$ (i.e., $\sup \text{range}(f) = \alpha$).
  - Depends: DEF-SET001 (ordinal), PRIM-BST009 (function)
  - Ownership: OWNS
  - Fragment: FOL
  - Condition for inclusion: needed for Konig's theorem and advanced model theory.

- DEF-SET015: **Continuum Hypothesis (CH)** [Deferred]
  - Definition: $2^{\aleph_0} = \aleph_1$. The claim that there is no cardinal strictly between $\aleph_0$ and $2^{\aleph_0}$. Independent of ZFC (Godel: consistent with ZFC; Cohen: negation consistent with ZFC).
  - Depends: DEF-SET007 (cardinal), DEF-SET008 (cardinality), AX-SET004 (Power Set)
  - Ownership: OWNS
  - Fragment: FOL
  - Condition for inclusion: mentioned as a notable independence result; detailed treatment only if relevant to a composition pattern.

## 6. Key Theorems

- THM-SET001: **Well-Ordering Theorem $\iff$ Zorn's Lemma $\iff$ AC**
  - Statement: The following are equivalent (over ZF): (a) Every set can be well-ordered. (b) Zorn's Lemma. (c) The Axiom of Choice.
  - Depends: AX-SET009 (Choice), DEF-SET009 (well-ordering), DEF-SET010 (Zorn's Lemma)
  - Proof sketch: AC $\to$ Well-Ordering: by transfinite recursion, build a well-ordering using a choice function. Well-Ordering $\to$ Zorn: given a chain-bounded partial order, well-order the underlying set and build a maximal chain. Zorn $\to$ AC: apply Zorn to the partial order of partial choice functions.
  - Source: SRC-SET001 (Kunen Ch. 1)

- THM-SET002: **Transfinite Recursion Theorem**
  - Statement: For any class function $G : V \to V$, there exists a unique function $F : \text{Ord} \to V$ such that $F(\alpha) = G(F \upharpoonright \alpha)$ for all ordinals $\alpha$.
  - Depends: DEF-SET006 (transfinite recursion), AX-SET007 (Replacement)
  - Proof sketch: Define $F$ as the union of all "approximations" $f$ defined on initial segments of the ordinals. Replacement ensures each approximation is a set. Uniqueness by transfinite induction.
  - Source: SRC-SET001 (Kunen Ch. 1)

- THM-SET003: **Cantor's Theorem (in ZFC)**
  - Statement: For every set $A$, $|A| < |\mathcal{P}(A)|$.
  - Depends: DEF-SET011 (Cantor's theorem)
  - Proof sketch: Same diagonal argument as THM-BST001, now justified within ZFC using Separation (to define the diagonal set $D = \{a \in A : a \notin f(a)\}$).
  - Source: SRC-SET003 (Enderton Ch. 6)

## 7. Invariants & Constraints

- INV-SET001: **Well-Foundedness of $\in$**
  - Statement: The membership relation $\in$ is well-founded on the universe of sets: there is no infinite descending chain $\ldots \in x_2 \in x_1 \in x_0$.
  - Justification: Guaranteed by AX-SET008 (Foundation).

- INV-SET002: **No Universal Set**
  - Statement: There is no set of all sets. $V = \{x : x = x\}$ is a proper class, not a set.
  - Justification: If $V$ were a set, Russell's paradox would apply via Separation: $\{x \in V : x \notin x\}$ leads to contradiction.

- FORBID-SET001: **Unrestricted Comprehension**
  - Statement: The schema $\exists y\, \forall x\, (x \in y \leftrightarrow \varphi(x))$ (unrestricted) is FORBIDDEN — it is not an axiom of ZFC. Only Separation (AX-SET006, which requires $x \in A$ for some existing set $A$) is used.
  - Consequence: Unrestricted comprehension leads to Russell's paradox: $\{x : x \notin x\}$ leads to $R \in R \iff R \notin R$.

## 8. Extension Points

- EXT-SET001: **Large Cardinal Axioms (Additive)**
  - Fixed: ZFC axioms.
  - Parameterizable: Add axioms asserting the existence of "large" cardinals (inaccessible, Mahlo, measurable, supercompact, etc.). These are stronger consistency-strength axioms.
  - Extension type: Additive
  - Examples: "There exists an inaccessible cardinal" — cannot be proved from ZFC alone (if ZFC is consistent).

- EXT-SET002: **Alternative Set Theories (Replacement)**
  - Fixed: The concept of axiomatic set theory as a first-order theory.
  - Parameterizable: Replace ZFC with alternative axiomatizations: ZF (no Choice), NBG (classes as first-class objects), MK (Morse-Kelley, stronger class comprehension), NF (Quine's New Foundations).
  - Extension type: Replacement
  - Examples: ZF is used in constructive contexts; NBG adds a finite number of class existence axioms.

## 9. Intra-Domain Dependency Graph

```
PRIM-SET001 (Set, formal) --- PRIM-SET002 (Membership, formal)
     |                              |
     v                              v
PRIM-SET003 (Class)           AX-SET001 (Extensionality)
                              AX-SET002 (Pairing)
                              AX-SET003 (Union)
                              AX-SET004 (Power Set)
                              AX-SET005 (Infinity)
                              AX-SET006 (Separation)
                              AX-SET007 (Replacement)
                              AX-SET008 (Foundation)
                              AX-SET009 (Choice)
                                   |
                                   v
                              DEF-SET001 (Ordinal)
                                   |
                                   +---> DEF-SET002 (Successor Ordinal)
                                   +---> DEF-SET003 (Limit Ordinal)
                                   +---> DEF-SET004 (omega)
                                   +---> DEF-SET005 (Transfinite Induction)
                                   +---> DEF-SET006 (Transfinite Recursion)
                                   |
                                   v
                              DEF-SET007 (Cardinal) --> DEF-SET008 (Cardinality)
                              DEF-SET009 (Well-Ordering)
                              DEF-SET010 (Zorn's Lemma)
                              DEF-SET011 (Cantor's Theorem, formal)
                              [Deferred: DEF-SET012--015]
```

## 10. Cross-Domain Interface

### Exports

| ID | Concept | Consumed by |
|----|---------|-------------|
| PRIM-SET001 | Set (formal) | SEM (models of ZFC) |
| PRIM-SET002 | Membership ($\in$, formal) | SYN (relation symbol of $\mathcal{L}_\in$) |
| PRIM-SET003 | Class | — |
| AX-SET001--009 | ZFC Axioms | DED (proofs within ZFC), SEM (models of ZFC) |
| DEF-SET001 | Ordinal | SEM |
| DEF-SET004 | $\omega$ | SEM, CMP |
| DEF-SET005 | Transfinite Induction | SEM |
| DEF-SET006 | Transfinite Recursion | SEM |
| DEF-SET007 | Cardinal | SEM |
| DEF-SET008 | Cardinality (formal) | SEM |
| DEF-SET009 | Well-Ordering | SEM |
| DEF-SET010 | Zorn's Lemma | DED, SEM |

### Imports

| ID | Concept | Provided by |
|----|---------|-------------|
| PRIM-BST001 | Set (naive) | BST |
| PRIM-BST009 | Function | BST |
| PRIM-BST012 | Natural Number | BST |
| PRIM-BST013 | Mathematical Induction | BST |
| DEF-BST003 | Bijection | BST |
| DEF-BST005 | Partial Order | BST |
| PRIM-SYN009 | Language | SYN |
| PRIM-SYN012 | Formula | SYN |
| PRIM-SYN013 | Sentence | SYN |
| PRIM-SYN018 | Equality Symbol | SYN |
| PRIM-SEM001 | Structure | SEM |
| PRIM-SEM011 | Model | SEM |
| PRIM-DED002 | Non-Logical Axiom | DED |
| PRIM-DED006 | Provability | DED |

## 11. Completeness Argument

**Why these primitives + axioms + definitions cover the domain**: The 3 primitives + 9 axioms + 11 core definitions provide:
- **Primitives**: The language $\mathcal{L}_\in = \{\in\}$ (PRIM-SET001, SET002) plus informal class notation (SET003).
- **Axioms**: The full ZFC axiom system (AX-SET001--009).
- **Ordinal theory**: ordinals (DEF-001--003), $\omega$ (004), transfinite induction/recursion (005--006).
- **Cardinal theory**: cardinals (007), cardinality (008), Cantor's theorem (011).
- **Well-ordering**: well-ordering (009), Zorn's lemma (010).

**Scope check**: per ASM-SET002, we include only what's needed for logic. CP-002 (Completeness) uses Zorn's lemma. CP-003 (Compactness) uses cardinality. CP-004 (Lowenheim-Skolem) uses cardinals. CP-005/006 (Incompleteness) use $\omega$ as the domain of arithmetic. All required items are present.

**OL chapters**: `content/set-theory/`.

## 12. OpenLogic Mapping

| OL Chapter/Section | Maps to |
|---|---|
| `content/set-theory/` (general) | PRIM-SET001--003, AX-SET001--009 |
| `content/set-theory/ordinals/` (if present) | DEF-SET001--004, DEF-SET005--006 |
| `content/set-theory/cardinals/` (if present) | DEF-SET007--008, DEF-SET011 |
| `content/sets-functions-relations/` (foundational) | BST (Level-0); SET provides formal backing |

## 13. Self-Audit Checklist

- [x] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [x] Every THM depends only on previously listed AX/DEF/THM
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports
- [x] Dissolution argument is present and non-trivial
- [x] Extension points cover applicable types: additive (large cardinals), replacement (alternative set theories)
- [x] Intra-domain dependency graph is acyclic
- [x] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [x] Motivating examples are present for all PRIM and key DEF entries
- [x] No PRIM/DEF duplicates an entry in another domain (BST owns naive set/membership; SET owns formal versions; P5 applied)
- [x] Completeness argument addresses all relevant OL chapters
