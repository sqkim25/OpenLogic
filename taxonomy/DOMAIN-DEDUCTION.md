# DOMAIN-DEDUCTION v0.1

## 0. Sources & Assumptions

- SRC-DED001: Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Ch. 2 (Hilbert-style proof system)
- SRC-DED002: Gentzen, "Investigations into logical deduction," 1935 (natural deduction, sequent calculus)
- SRC-DED003: Smullyan, *First-Order Logic*, 1968 (tableaux / analytic tableaux)
- ASM-DED001: We present the abstract notion of "proof system" as a primitive, then instantiate it with four standard architectures (Hilbert, ND, SC, Tableaux) as parameterized definitions. Justification: resolves UNK-GLB002 — the architectures are not independent primitives but variants of the same abstract concept.
- ASM-DED002: Our default Hilbert-style system uses the axiom schemas and rules from Enderton Ch. 2. Other textbooks choose different axiom sets; these are noted as variants. Justification: SRC-DED001.
- UNK-DED001: Resolution of UNK-GLB002 — proof system architectures are parameterized variants of a single abstract concept (PRIM-DED004 "proof system"), not separate primitives. Resolved.

## 1. Domain Intent

- **Irreducible question**: How are truths derived from assumptions?
- **Scope**: Syntactic consequence ($\vdash$), proof systems, rules of inference, derivations, and the formal apparatus for establishing that a formula follows from given assumptions by purely mechanical, step-by-step reasoning. This domain covers the "proof side" of logic — purely syntactic, no reference to truth or meaning.
- **Non-goals**: What formulas mean (SEM). Whether proofs can be found algorithmically (CMP — though decidability of proof-checking is noted). The formal theory of sets (SET). The connection between $\vdash$ and $\vDash$ (composition patterns CP-001, CP-002).
- **Dissolution argument**: Syntactic consequence ($\vdash$) is a formal, combinatorial notion about symbol manipulation following rules. It is distinct from semantic consequence ($\vDash$) — the completeness theorem bridges them, but this bridge is a non-trivial result (CP-002). DED cannot be merged into SYN because deduction involves *sequences* of formulas organized by rules (not just formation of individual formulas). A "derivation" is a structured object (sequence, tree, or tableau) built according to specific inference rules — this goes beyond SYN's concern with individual well-formed expressions. DED cannot be merged into SEM because proof systems are purely syntactic objects that can be studied without any notion of truth. One can verify a proof is correct without knowing whether the conclusion is "true" — it is a purely mechanical check of rule applications.

## 2. Prerequisites

- DEP-DED001: Requires SYN for PRIM-SYN012 (formula), PRIM-SYN013 (sentence), PRIM-SYN003 (connective), PRIM-SYN004 (quantifier), DEF-SYN001 (substitution), DEF-SYN003 (free variables), PRIM-SYN014 (free occurrence)
- DEP-DED002: Requires BST for PRIM-BST001 (set), PRIM-BST009 (function), PRIM-BST010 (finite sequence), PRIM-BST012 (natural number), PRIM-BST013 (mathematical induction)

## 3. Primitive Notions

- PRIM-DED001: **Axiom Schema (Logical Axiom)**
  - Description: A template that generates infinitely many axioms by substituting formulas for schematic variables. Logical axiom schemas are the starting points of a proof system — formulas that are assumed derivable without proof. They capture the "logical truths" that hold regardless of the specific language or interpretation.
  - Formal: An axiom schema is a meta-expression with schematic variables $\varphi, \psi, \theta$ such that every substitution instance is a logical axiom. Example (Enderton): $\varphi \to (\psi \to \varphi)$.
  - Ownership: OWNS
  - Source: SRC-DED001 (Enderton Ch. 2), SRC-GLB003 (Mendelson Ch. 2)
  - Referenced by: SEM (axiom schemas validated by soundness), CMP (axiom schemas are computably enumerable)
  - Fragment: both (PL axiom schemas use only propositional formulas)
  - Motivating example: The axiom schema $\varphi \to (\psi \to \varphi)$ generates instances like $P(x) \to (Q(y) \to P(x))$ and $(p \land q) \to (r \to (p \land q))$. Each instance is a logical axiom.

- PRIM-DED002: **Non-Logical Axiom (Proper Axiom)**
  - Description: A specific sentence assumed as a starting point for a particular theory, as opposed to logical axioms which hold universally. Non-logical axioms define the specific subject matter of a theory.
  - Formal: A sentence $\varphi$ designated as an axiom of a theory $T$. The set of non-logical axioms is denoted $\Lambda$ or $T_{\text{ax}}$.
  - Ownership: OWNS
  - Source: SRC-DED001 (Enderton Ch. 2)
  - Referenced by: SEM (non-logical axioms determine which structures are models), SET (ZFC axioms are non-logical axioms)
  - Fragment: FOL (PL typically uses only logical axioms)
  - Motivating example: The group axioms: $\forall x\, (e \cdot x = x)$, $\forall x\, \exists y\, (x \cdot y = e)$, $\forall x\, \forall y\, \forall z\, ((x \cdot y) \cdot z = x \cdot (y \cdot z))$. The Peano axioms for arithmetic.

- PRIM-DED003: **Rule of Inference**
  - Description: A syntactic rule that permits deriving a new formula (the conclusion) from zero or more already-derived formulas (the premises). Rules of inference are the "moves" in a proof. Each rule specifies a pattern: if formulas matching the premise pattern have been derived, then the conclusion may be written down.
  - Formal: A rule $\frac{\varphi_1 \quad \cdots \quad \varphi_n}{\psi}$ where $\varphi_1, \ldots, \varphi_n$ are premise schemas and $\psi$ is a conclusion schema.
  - Ownership: OWNS
  - Source: SRC-GLB009 (Gentzen 1935), SRC-DED001 (Enderton Ch. 2)
  - Referenced by: SEM (rules validated by soundness — each rule preserves truth), CMP (rule application is a computable step)
  - Fragment: both
  - Motivating example: Modus Ponens: $\frac{\varphi \quad \varphi \to \psi}{\psi}$. Universal Generalization: $\frac{\varphi}{\forall x\, \varphi}$ (with side conditions on $x$).

- PRIM-DED004: **Proof System (Formal Deductive System)**
  - Description: A specification consisting of: (1) a set of logical axiom schemas, (2) a set of rules of inference, and (3) optionally, structural conventions (e.g., what counts as a derivation object — sequence, tree, tableau). A proof system determines what can be derived from what. Different proof systems (Hilbert, ND, SC, Tableaux) are architecturally different but equivalent in deductive power for classical FOL.
  - Formal: $\mathcal{S} = \langle \text{AxiomSchemas}, \text{Rules}, \text{DerivationFormat} \rangle$.
  - Ownership: OWNS
  - Source: SRC-DED001, SRC-DED002, SRC-DED003
  - Referenced by: SEM (each proof system validated by soundness), CMP (proof systems are effective — derivation checking is decidable)
  - Fragment: both
  - Motivating example: Enderton's Hilbert system for FOL: axiom schemas (tautology instances, distribution, contraposition, quantifier axioms, equality axioms) + rules (MP, Gen).

- PRIM-DED005: **Derivation**
  - Description: A finite structured object (sequence, tree, or tableau, depending on the proof system) that witnesses the derivability of a formula from given assumptions, by recording each step as either an axiom, an assumption, or a result of applying a rule to previously derived formulas.
  - Formal: In a Hilbert system: a finite sequence $\langle \varphi_1, \varphi_2, \ldots, \varphi_n \rangle$ where each $\varphi_i$ is either a logical axiom, a member of $\Gamma$ (assumption set), or follows from earlier formulas by a rule of inference.
  - Ownership: OWNS
  - Source: SRC-DED001 (Enderton Ch. 2), SRC-GLB009 (Gentzen 1935)
  - Referenced by: SEM (derivations are what soundness analyzes), CMP (derivations are finite, checkable objects)
  - Fragment: both
  - Motivating example: A Hilbert-style derivation of $q$ from $\{p, p \to q\}$: (1) $p$ [assumption], (2) $p \to q$ [assumption], (3) $q$ [MP on 1, 2].

- PRIM-DED006: **Provability ($\Gamma \vdash \varphi$)**
  - Description: The central relation of deduction: formula $\varphi$ is provable (derivable) from assumption set $\Gamma$ in proof system $\mathcal{S}$. This means there exists a derivation of $\varphi$ from $\Gamma$. When $\Gamma = \emptyset$, we write $\vdash \varphi$ and say $\varphi$ is a theorem of the proof system.
  - Formal: $\Gamma \vdash_{\mathcal{S}} \varphi$ iff there exists a derivation of $\varphi$ from $\Gamma$ in $\mathcal{S}$.
  - Ownership: OWNS
  - Source: SRC-DED001 (Enderton Ch. 2)
  - Referenced by: SEM (soundness: $\Gamma \vdash \varphi \Rightarrow \Gamma \vDash \varphi$; completeness: $\Gamma \vDash \varphi \Rightarrow \Gamma \vdash \varphi$), CMP (provability is c.e. / semi-decidable)
  - Fragment: both
  - Motivating example: $\{P(a), \forall x\,(P(x) \to Q(x))\} \vdash Q(a)$. $\vdash (p \to p)$ (a PL theorem).

- PRIM-DED007: **Structural Rule**
  - Description: A rule governing how the set of assumptions is managed, independent of the specific logical connectives. The standard structural rules are: Weakening (adding unused assumptions), Contraction (collapsing duplicate assumptions), Exchange (reordering assumptions), and Cut (chaining derivations via an intermediate formula). These are "about the structure of proof" rather than about specific logical operators.
  - Formal: Weakening: $\frac{\Gamma \vdash \varphi}{\Gamma, \psi \vdash \varphi}$. Contraction: $\frac{\Gamma, \psi, \psi \vdash \varphi}{\Gamma, \psi \vdash \varphi}$. Exchange: $\frac{\Gamma, \psi, \chi, \Delta \vdash \varphi}{\Gamma, \chi, \psi, \Delta \vdash \varphi}$. Cut: $\frac{\Gamma \vdash \psi \quad \Delta, \psi \vdash \varphi}{\Gamma, \Delta \vdash \varphi}$.
  - Ownership: OWNS
  - Source: SRC-GLB009 (Gentzen 1935), SRC-DED002
  - Referenced by: (internal — structural rules are modified in substructural logic extensions)
  - Fragment: both
  - Motivating example: Weakening justifies adding irrelevant hypotheses: if we can derive $q$ from $\{p\}$, we can derive $q$ from $\{p, r\}$. Cut justifies using lemmas: derive a lemma, then use it.

- PRIM-DED008: **Sequent ($\Gamma \Rightarrow \Delta$)**
  - Description: A formal expression representing a derivability claim in sequent calculus. $\Gamma \Rightarrow \Delta$ asserts: "from the assumptions $\Gamma$, at least one of the conclusions $\Delta$ follows." In classical logic, $\Gamma \Rightarrow \Delta$ is valid iff $\bigwedge \Gamma \to \bigvee \Delta$ is valid. The double-arrow $\Rightarrow$ distinguishes sequent notation from the object-language conditional $\to$.
  - Formal: $\Gamma \Rightarrow \Delta$ where $\Gamma$ (antecedent) and $\Delta$ (succedent) are finite multisets (or sequences) of formulas.
  - Ownership: OWNS
  - Source: SRC-GLB009 (Gentzen 1935)
  - Referenced by: SEM (sequent validity corresponds to semantic consequence)
  - Fragment: both
  - Motivating example: $P(a), \forall x\,(P(x) \to Q(x)) \Rightarrow Q(a)$ is a valid sequent. $\Rightarrow P(a) \lor \neg P(a)$ asserts the law of excluded middle (empty antecedent).

- PRIM-DED009: **Assumption Discharge**
  - Description: In natural deduction, some rules allow you to "use" a temporary assumption and then "discharge" (cancel) it, recording that the conclusion no longer depends on that assumption. Discharging is the mechanism by which conditional proofs work: to prove "if $\varphi$ then $\psi$," assume $\varphi$, derive $\psi$, then discharge $\varphi$.
  - Formal: In $\to$-introduction: from a derivation of $\psi$ using assumption $\varphi$ (among others), derive $\varphi \to \psi$ and discharge all occurrences of $\varphi$. The resulting derivation depends on whatever assumptions were NOT discharged.
  - Ownership: OWNS
  - Source: SRC-GLB009 (Gentzen 1935), SRC-DED002
  - Referenced by: SEM (discharge corresponds semantically to conditional reasoning)
  - Fragment: both
  - Motivating example: To prove $\vdash p \to p$: (1) assume $p$ [assumption]; (2) derive $p \to p$ [$\to$-introduction, discharging assumption $p$]. The final result depends on no assumptions.

- PRIM-DED010: **Theorem**
  - Description: A formula derivable from the empty set of assumptions (or from the logical axioms alone, in Hilbert systems). Theorems are the "provable truths" of a proof system — they hold unconditionally.
  - Formal: $\varphi$ is a theorem iff $\vdash \varphi$ (i.e., $\emptyset \vdash \varphi$).
  - Ownership: OWNS
  - Source: SRC-DED001 (Enderton Ch. 2)
  - Referenced by: SEM (soundness: every theorem is valid), CMP (the set of theorems is c.e.)
  - Fragment: both
  - Motivating example: $\vdash (p \to p)$ is a PL theorem. $\vdash \forall x\, (x = x)$ is an FOL theorem (from the equality axiom schema).

## 4. Axioms

- AX-DED001: **Modus Ponens (MP)**
  - Statement: If $\Gamma \vdash \varphi$ and $\Gamma \vdash (\varphi \to \psi)$, then $\Gamma \vdash \psi$.
  - Description: The rule of inference that, given a derivation of $\varphi$ and a derivation of $\varphi \to \psi$, produces a derivation of $\psi$. It is the fundamental elimination rule for the conditional connective. MP is a specific named instance of the primitive PRIM-DED003 (rule of inference).
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED006 (provability), PRIM-SYN003 (logical connective, specifically $\to$)
  - Source: SRC-GLB001 (Enderton Ch. 2), SRC-GLB009 (Gentzen, as "$\to$-elimination")
  - Normative: MUST (every Hilbert-style system includes MP; equivalent in ND via $\to$-elimination)
  - Natural language: Given any two already-derived statements where one is "if A then B" and the other is "A," you may derive "B."
  - Motivating example: From "It is raining" ($p$) and "If it is raining then the ground is wet" ($p \to q$), derive "The ground is wet" ($q$). Formally: from $\{p, p \to q\} \vdash p$ and $\{p, p \to q\} \vdash (p \to q)$, conclude $\{p, p \to q\} \vdash q$.

- AX-DED002: **Universal Generalization (Gen)**
  - Statement: If $\Gamma \vdash \varphi$ and $x$ does not occur free in any formula in $\Gamma$, then $\Gamma \vdash \forall x\, \varphi$.
  - Description: The rule that permits concluding "for all $x$, $\varphi$" from a derivation of $\varphi$, provided $x$ was not assumed to have any particular property in the assumptions. The side condition on $x$ is essential — without it, the rule would be unsound.
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED006 (provability), PRIM-SYN004 (quantifier), PRIM-SYN014 (free occurrence)
  - Source: SRC-DED001 (Enderton Ch. 2)
  - Normative: MUST (for FOL; not present in PL systems)
  - Natural language: If you've proved something about an arbitrary $x$ (not assumed to be any specific object), then you can conclude it holds for all $x$.
  - Motivating example: From $\vdash P(x) \to P(x)$ (where $x$ is free and no assumption mentions $x$), derive $\vdash \forall x\, (P(x) \to P(x))$.

- AX-DED003: **Logical Axiom Schemas (Hilbert-style)**
  - Statement: The following are logical axiom schemas (every substitution instance is a logical axiom):
    - (A1) $\varphi \to (\psi \to \varphi)$
    - (A2) $(\varphi \to (\psi \to \theta)) \to ((\varphi \to \psi) \to (\varphi \to \theta))$
    - (A3) $(\neg \psi \to \neg \varphi) \to (\varphi \to \psi)$
    - (A4) $\forall x\, \varphi \to \varphi[t/x]$ (where $t$ is substitutable for $x$ in $\varphi$)
    - (A5) $\forall x\, (\varphi \to \psi) \to (\varphi \to \forall x\, \psi)$ (where $x$ is not free in $\varphi$)
    - (A6) $x = x$ (reflexivity of equality)
    - (A7) $x = y \to (\varphi \to \varphi')$ (where $\varphi'$ is obtained from $\varphi$ by replacing some free occurrences of $x$ by $y$)
  - Description: These schemas, together with MP and Gen, form a complete proof system for classical FOL with equality (Enderton's system).
  - Depends: PRIM-DED001 (axiom schema), PRIM-SYN003 (connective), PRIM-SYN004 (quantifier), PRIM-SYN018 (equality), DEF-SYN001 (substitution)
  - Source: SRC-DED001 (Enderton Ch. 2)
  - Normative: MUST (for this specific Hilbert-style system; other Hilbert systems use different but equivalent axiom sets)
  - Natural language: Schemas A1--A3 handle propositional reasoning. A4 handles universal instantiation. A5 handles distribution of $\forall$ over $\to$. A6--A7 handle equality reasoning.

## 5. Definitions (Conservative Extensions)

- DEF-DED001: **Syntactic Consistency ($\Gamma \nvdash \bot$)**
  - Definition: A set of formulas $\Gamma$ is syntactically consistent if there is no formula $\varphi$ such that both $\Gamma \vdash \varphi$ and $\Gamma \vdash \neg \varphi$. Equivalently, $\Gamma$ does not derive every formula (since from a contradiction, everything follows via explosion).
  - Formal: $\Gamma$ is consistent iff there is no $\varphi$ with $\Gamma \vdash \varphi$ and $\Gamma \vdash \neg \varphi$. Equivalently: $\Gamma$ is consistent iff it is not the case that $\Gamma \vdash \varphi$ for ALL $\varphi$.
  - Depends: PRIM-DED006 (provability), PRIM-SYN003 (connective, specifically $\neg$)
  - Ownership: OWNS (syntactic consistency; semantic consistency is DEF-SEM004 in SEM. Boundary: P2)
  - Referenced by: SEM (linked to semantic consistency via CP-001/CP-002), CMP (consistency is not decidable for sufficiently strong theories)
  - Fragment: both
  - Motivating example: $\{P(a), \neg P(a)\}$ is syntactically inconsistent (derives both $P(a)$ and $\neg P(a)$ trivially). The Peano axioms are syntactically consistent (by Godel's 2nd theorem, this cannot be proved within PA itself).

- DEF-DED002: **Maximal Consistent Set**
  - Definition: A consistent set of formulas $\Gamma$ that cannot be extended by any formula without becoming inconsistent. For every sentence $\varphi$: either $\varphi \in \Gamma$ or $\neg \varphi \in \Gamma$.
  - Formal: $\Gamma$ is maximal consistent iff: (i) $\Gamma$ is consistent; (ii) for every sentence $\varphi$, either $\varphi \in \Gamma$ or $\neg \varphi \in \Gamma$.
  - Depends: DEF-DED001 (consistency), PRIM-SYN013 (sentence)
  - Ownership: OWNS
  - Referenced by: SEM (Lindenbaum's lemma: every consistent set extends to a maximal one — key step in Henkin completeness proof)
  - Fragment: both
  - Motivating example: $\text{Th}(\mathfrak{N})$ (the set of all sentences true in $\mathfrak{N}$) is maximal consistent (for every sentence, either it or its negation is true in $\mathfrak{N}$, and no contradiction is derivable).

- DEF-DED003: **Deductive Closure ($\text{Cn}(\Gamma)$)**
  - Definition: The set of all formulas derivable from $\Gamma$ — the "consequences" of $\Gamma$ according to the proof system.
  - Formal: $\text{Cn}(\Gamma) = \{\varphi : \Gamma \vdash \varphi\}$.
  - Depends: PRIM-DED006 (provability)
  - Ownership: OWNS
  - Referenced by: SEM (deductive closure related to theory of a structure via completeness)
  - Fragment: both
  - Motivating example: If $\Gamma = \{p, p \to q\}$, then $\text{Cn}(\Gamma)$ includes $p$, $q$, $p \to q$, $q \to q$, and every tautology, among others.

- DEF-DED004: **Conservative Extension**
  - Definition: A theory $T'$ is a conservative extension of $T$ (in language $\mathcal{L} \subseteq \mathcal{L}'$) if every $\mathcal{L}$-sentence provable in $T'$ is already provable in $T$. Adding the new symbols and axioms of $T'$ does not yield new theorems in the old language.
  - Formal: $T'$ is a conservative extension of $T$ iff for every $\mathcal{L}$-sentence $\varphi$: $T' \vdash \varphi \Rightarrow T \vdash \varphi$.
  - Depends: PRIM-DED006 (provability), PRIM-SYN009 (language), PRIM-SYN013 (sentence)
  - Ownership: OWNS
  - Referenced by: SET (ZFC extensions), CMP (definitional extensions of arithmetic)
  - Fragment: FOL
  - Motivating example: Adding a new constant symbol $c$ to PA with the axiom $c = S(S(0))$ is a conservative extension — anything provable about the natural numbers using $c$ was already provable without it (using $S(S(0))$ directly).

- DEF-DED005: **Hilbert-Style Proof System**
  - Definition: A proof system architecture where derivations are finite sequences of formulas. The system is defined by a (typically small) set of axiom schemas and a few rules (usually just MP, plus Gen for FOL). Proofs are linear sequences.
  - Formal: $\mathcal{H} = \langle \text{AxiomSchemas}, \{MP, Gen\} \rangle$. A derivation is a sequence $\langle \varphi_1, \ldots, \varphi_n \rangle$ where each $\varphi_i$ is an axiom instance, a member of $\Gamma$, or follows from earlier items by MP or Gen.
  - Depends: PRIM-DED001 (axiom schema), PRIM-DED003 (rule of inference), PRIM-DED004 (proof system), PRIM-DED005 (derivation), AX-DED001 (MP), AX-DED002 (Gen), AX-DED003 (axiom schemas)
  - Ownership: OWNS
  - Referenced by: SEM (Henkin completeness proof typically uses Hilbert system), CMP (Hilbert proofs are easily Godel-numbered)
  - Fragment: both (PL Hilbert system: schemas A1--A3 + MP)
  - Motivating example: Enderton's system (AX-DED003 + MP + Gen) is a Hilbert-style system. Mendelson's system uses a different axiom set but is equivalent.

- DEF-DED006: **Natural Deduction System (ND)**
  - Definition: A proof system architecture where derivations are trees (or Fitch-style nested subproofs). Instead of many axiom schemas, ND has introduction and elimination rules for each connective and quantifier. Assumptions can be temporarily introduced and later discharged.
  - Formal: $\mathcal{ND} = \langle \emptyset, \{\to\text{-I}, \to\text{-E}, \land\text{-I}, \land\text{-E}, \lor\text{-I}, \lor\text{-E}, \neg\text{-I}, \neg\text{-E}, \forall\text{-I}, \forall\text{-E}, \exists\text{-I}, \exists\text{-E}\} \rangle$. Derivations are trees with leaves as assumptions (open or discharged).
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED004 (proof system), PRIM-DED009 (assumption discharge)
  - Ownership: OWNS
  - Referenced by: SEM (alternative proofs of completeness), CMP (Curry-Howard correspondence connects ND proofs to lambda terms)
  - Fragment: both (PL ND: connective rules only)
  - Motivating example: To prove $p \to (q \to p)$ in ND: (1) assume $p$; (2) assume $q$; (3) have $p$ [reiteration]; (4) discharge $q$, conclude $q \to p$; (5) discharge $p$, conclude $p \to (q \to p)$.

- DEF-DED007: **Sequent Calculus (SC)**
  - Definition: A proof system architecture where the objects of derivation are sequents ($\Gamma \Rightarrow \Delta$) rather than formulas. Rules manipulate sequents by adding, removing, or transforming formulas in the antecedent or succedent. The system has structural rules (weakening, contraction, exchange, cut) and logical rules (left/right introduction for each connective/quantifier).
  - Formal: $\mathcal{SC} = \langle \{\text{Identity}\}, \text{StructuralRules} \cup \text{LogicalRules} \rangle$. Initial sequent (axiom): $\varphi \Rightarrow \varphi$. Derivations are trees of sequents.
  - Depends: PRIM-DED004 (proof system), PRIM-DED007 (structural rule), PRIM-DED008 (sequent)
  - Ownership: OWNS
  - Referenced by: SEM (cut-free proofs have the subformula property — useful for analysis), CMP (sequent calculus proofs analyzable for complexity)
  - Fragment: both
  - Motivating example: Proof of $\Rightarrow P(a) \lor \neg P(a)$ in SC: start with $P(a) \Rightarrow P(a)$, apply $\neg$-right to get $\Rightarrow P(a), \neg P(a)$, apply $\lor$-right to get $\Rightarrow P(a) \lor \neg P(a)$.

- DEF-DED008: **Tableau System (Analytic Tableaux)**
  - Definition: A proof system architecture that works by attempted refutation. To prove $\varphi$, assume $\neg \varphi$ and systematically decompose it into simpler formulas, branching when disjunctive decomposition occurs. If every branch closes (contains a contradiction), the original formula is valid.
  - Formal: $\mathcal{Tab} = \langle \emptyset, \text{ExpansionRules} \cup \{\text{Closure}\} \rangle$. A tableau is a labeled tree. Branches close when they contain both $\varphi$ and $\neg \varphi$ for some $\varphi$.
  - Depends: PRIM-DED004 (proof system), PRIM-SYN017 (subformula)
  - Ownership: OWNS
  - Referenced by: CMP (tableaux can serve as decision procedures for PL)
  - Fragment: both
  - Motivating example: To test validity of $((p \to q) \to p) \to p$ (Peirce's law): negate to get $\neg(((p \to q) \to p) \to p)$; decompose: $(p \to q) \to p$ and $\neg p$; decompose $\to$: branch on $\neg(p \to q)$ or $p$. The $p$ branch closes with $\neg p$. The $\neg(p \to q)$ branch gives $p$ and $\neg q$; $p$ closes with $\neg p$. All branches close: Peirce's law is valid.

- DEF-DED009: **Derived Rule**
  - Definition: A rule of inference that is not a primitive rule of the system but can be established as a shortcut by showing that its conclusion is derivable from its premises using the primitive rules. Derived rules simplify proofs without extending the proof system's power.
  - Formal: A derived rule $\frac{\varphi_1 \cdots \varphi_n}{\psi}$ is justified by exhibiting a derivation of $\psi$ from $\varphi_1, \ldots, \varphi_n$ using only primitive rules.
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED005 (derivation)
  - Ownership: OWNS
  - Referenced by: (internal — derived rules simplify later proofs)
  - Fragment: both
  - Motivating example: Modus Tollens ($\frac{\varphi \to \psi \quad \neg \psi}{\neg \varphi}$) is derivable from MP + axiom schemas in a Hilbert system. Hypothetical Syllogism ($\frac{\varphi \to \psi \quad \psi \to \theta}{\varphi \to \theta}$) is derived.

- DEF-DED010: **Admissible Rule**
  - Definition: A rule $\frac{\varphi_1 \cdots \varphi_n}{\psi}$ is admissible for a proof system if: whenever $\vdash \varphi_1, \ldots, \vdash \varphi_n$ are all provable, then $\vdash \psi$ is provable. Unlike derived rules, admissible rules need not produce a derivation that uses the premises directly — only the provability of the conclusion is guaranteed.
  - Formal: $\frac{\varphi_1 \cdots \varphi_n}{\psi}$ is admissible iff $(\vdash \varphi_1 \land \cdots \land \vdash \varphi_n) \Rightarrow \vdash \psi$.
  - Depends: PRIM-DED006 (provability), PRIM-DED010 (theorem)
  - Ownership: OWNS
  - Referenced by: (internal — admissibility is important for cut-elimination analysis)
  - Fragment: both
  - Motivating example: Cut is admissible in cut-free sequent calculus (Gentzen's Hauptsatz): if $\Gamma \Rightarrow \Delta, \varphi$ and $\varphi, \Gamma' \Rightarrow \Delta'$ are both provable without cut, then $\Gamma, \Gamma' \Rightarrow \Delta, \Delta'$ is also provable without cut.

## 6. Key Theorems

- THM-DED001: **Deduction Theorem (for Hilbert Systems)**
  - Statement: If $\Gamma \cup \{\varphi\} \vdash \psi$ (and no application of Gen in the derivation binds a variable free in $\varphi$), then $\Gamma \vdash \varphi \to \psi$.
  - Depends: PRIM-DED006 (provability), AX-DED001 (MP), AX-DED003 (axiom schemas A1, A2)
  - Proof sketch: By induction on the length of the derivation of $\psi$ from $\Gamma \cup \{\varphi\}$. If $\psi = \varphi$: $\vdash \varphi \to \varphi$ (provable from A1, A2, MP). If $\psi$ is an axiom or member of $\Gamma$: use A1 to get $\psi \to (\varphi \to \psi)$, then MP. If $\psi$ follows by MP from $\chi$ and $\chi \to \psi$: by induction, $\Gamma \vdash \varphi \to \chi$ and $\Gamma \vdash \varphi \to (\chi \to \psi)$; use A2 + MP.
  - Source: SRC-DED001 (Enderton Ch. 2, Corollary 24C)

- THM-DED002: **Equivalence of Proof Systems (for Classical FOL)**
  - Statement: For classical first-order logic: $\Gamma \vdash_{\mathcal{H}} \varphi$ iff $\Gamma \vdash_{\mathcal{ND}} \varphi$ iff $\Gamma \Rightarrow \varphi$ is derivable in $\mathcal{SC}$ iff the tableau for $\Gamma \cup \{\neg \varphi\}$ closes. All four proof system architectures derive exactly the same formulas.
  - Depends: DEF-DED005 (Hilbert), DEF-DED006 (ND), DEF-DED007 (SC), DEF-DED008 (Tableaux), PRIM-DED006 (provability)
  - Proof sketch: Shown by mutual simulation. Hilbert $\to$ ND: axiom schemas become derivable in ND. ND $\to$ SC: translate intro/elim rules to left/right rules. SC $\to$ Tableaux: relate sequent derivation trees to tableau trees. Tableaux $\to$ Hilbert: extract Hilbert-style proof from closed tableau.

- THM-DED003: **Cut Elimination (Gentzen's Hauptsatz)**
  - Statement: If a sequent $\Gamma \Rightarrow \Delta$ is derivable in sequent calculus, then it is derivable without using the cut rule.
  - Depends: DEF-DED007 (sequent calculus), PRIM-DED007 (structural rules, specifically cut)
  - Proof sketch: By double induction on (a) the complexity of the cut formula, and (b) the total size of the derivations of the cut premises. Key steps: reduce the complexity of the cut formula by "pushing it up" through the derivation. Gentzen's original proof used transfinite induction (up to $\epsilon_0$) for the first-order case.
  - Source: SRC-GLB009 (Gentzen 1935)

- THM-DED004: **Normalization (for Natural Deduction)**
  - Statement: Every ND derivation can be transformed into a "normal" derivation where no formula is both introduced and then immediately eliminated. Normal derivations have the subformula property.
  - Depends: DEF-DED006 (natural deduction)
  - Proof sketch: Analogous to cut elimination. Eliminate "detours" (introduction immediately followed by elimination) by replacing them with simpler derivations. Prawitz's strong normalization theorem: any sequence of reductions terminates.
  - Source: Prawitz, *Natural Deduction*, 1965

- THM-DED005: **Lindenbaum's Lemma**
  - Statement: Every syntactically consistent set of sentences can be extended to a maximal consistent set.
  - Depends: DEF-DED001 (consistency), DEF-DED002 (maximal consistent set)
  - Proof sketch: Enumerate all sentences as $\varphi_0, \varphi_1, \ldots$ (possible because the language is countable). Build $\Gamma_0 \subseteq \Gamma_1 \subseteq \cdots$ where $\Gamma_{n+1} = \Gamma_n \cup \{\varphi_n\}$ if consistent, else $\Gamma_{n+1} = \Gamma_n \cup \{\neg \varphi_n\}$. Take $\Gamma^* = \bigcup_n \Gamma_n$.
  - Source: SRC-DED001 (Enderton Ch. 2)

## 7. Invariants & Constraints

- INV-DED001: **Finite Derivability**
  - Statement: Every derivation is a finite object. $\Gamma \vdash \varphi$ means there is a FINITE derivation, even if $\Gamma$ is infinite (only finitely many members of $\Gamma$ are actually used).
  - Justification: Finiteness is essential for derivations to be checkable, and for the compactness theorem (via completeness: if $\Gamma \vdash \varphi$, then some finite $\Gamma_0 \subseteq \Gamma$ derives $\varphi$).

- INV-DED002: **Monotonicity (for Standard Classical Systems)**
  - Statement: $\Gamma \vdash \varphi$ and $\Gamma \subseteq \Delta$ implies $\Delta \vdash \varphi$. Adding more assumptions never invalidates a derivation.
  - Justification: Follows from the structural rule of weakening (PRIM-DED007). NOTE: substructural logics (EXT-DED003) may drop this.

- FORBID-DED001: **No Semantics in Proofs**
  - Statement: Derivations MUST be verifiable purely syntactically. No step in a derivation may appeal to "this formula is true" or "there exists a model." The concept $\vDash$ is NOT a concept of DED.
  - Consequence: Violation would make the soundness/completeness theorems (CP-001, CP-002) trivial or circular.

## 8. Extension Points

- EXT-DED001: **Modal Axiom Schemas and Rules (Additive)**
  - Fixed: The concept of axiom schema, rule of inference, and proof system.
  - Parameterizable: Add axiom schemas involving $\Box$/$\Diamond$ (e.g., K: $\Box(\varphi \to \psi) \to (\Box \varphi \to \Box \psi)$; T: $\Box \varphi \to \varphi$; 4: $\Box \varphi \to \Box \Box \varphi$; 5: $\Diamond \varphi \to \Box \Diamond \varphi$). Add the necessitation rule: $\frac{\vdash \varphi}{\vdash \Box \varphi}$.
  - Extension type: Additive
  - Examples: K, T, S4, S5 are determined by different combinations of modal axiom schemas.

- EXT-DED002: **Intuitionistic Restrictions (Replacement)**
  - Fixed: The concept of derivation and rules of inference.
  - Parameterizable: Remove (or weaken) rules that depend on the law of excluded middle: no double-negation elimination ($\neg \neg \varphi \to \varphi$), no classical reductio. In ND: restrict $\neg$-elimination. In SC: restrict the succedent to at most one formula (intuitionistic sequent calculus).
  - Extension type: Replacement
  - Examples: Intuitionistic logic (Heyting), minimal logic (Johansson).

- EXT-DED003: **Substructural Modifications (Structural)**
  - Fixed: The concept of rules and derivation.
  - Parameterizable: Remove structural rules: drop contraction (linear logic — resources are used exactly once), drop weakening (relevance logic — every assumption must be used), drop exchange (non-commutative logic — order of assumptions matters).
  - Extension type: Structural
  - Examples: Linear logic (Girard), relevance logic (Anderson & Belnap), Lambek calculus.

## 9. Intra-Domain Dependency Graph

```
PRIM-DED001 (Axiom Schema)
PRIM-DED002 (Non-Logical Axiom)
PRIM-DED003 (Rule of Inference)
     |
     +---> PRIM-DED004 (Proof System)
     |          |
     |          +---> DEF-DED005 (Hilbert)
     |          +---> DEF-DED006 (ND)
     |          +---> DEF-DED007 (SC)
     |          +---> DEF-DED008 (Tableaux)
     |
     +---> PRIM-DED005 (Derivation)
     |          |
     |          v
     |     PRIM-DED006 (Provability)
     |          |
     |          +---> PRIM-DED010 (Theorem)
     |          +---> DEF-DED001 (Syntactic Consistency)
     |          |          |
     |          |          +---> DEF-DED002 (Maximal Consistent Set)
     |          |
     |          +---> DEF-DED003 (Deductive Closure)
     |          +---> DEF-DED004 (Conservative Extension)
     |          +---> DEF-DED009 (Derived Rule)
     |          +---> DEF-DED010 (Admissible Rule)
     |
     +---> PRIM-DED007 (Structural Rule)
     +---> PRIM-DED008 (Sequent)
     +---> PRIM-DED009 (Assumption Discharge)

AX-DED001 (Modus Ponens) [depends: PRIM-DED003, PRIM-DED006]
AX-DED002 (Gen) [depends: PRIM-DED003, PRIM-DED006]
AX-DED003 (Logical Axiom Schemas) [depends: PRIM-DED001]
```

## 10. Cross-Domain Interface

### Exports

| ID | Concept | Consumed by |
|----|---------|-------------|
| PRIM-DED001 | Axiom Schema | SEM, CMP |
| PRIM-DED002 | Non-Logical Axiom | SEM, SET |
| PRIM-DED003 | Rule of Inference | SEM, CMP |
| PRIM-DED004 | Proof System | SEM, CMP |
| PRIM-DED005 | Derivation | SEM, CMP |
| PRIM-DED006 | Provability ($\vdash$) | SEM, CMP |
| PRIM-DED007 | Structural Rule | — |
| PRIM-DED008 | Sequent | — |
| PRIM-DED009 | Assumption Discharge | — |
| PRIM-DED010 | Theorem | SEM, CMP |
| DEF-DED001 | Syntactic Consistency | SEM, CMP |
| DEF-DED002 | Maximal Consistent Set | SEM |
| DEF-DED003 | Deductive Closure | SEM |
| DEF-DED004 | Conservative Extension | SET, CMP |
| DEF-DED005 | Hilbert-Style System | SEM, CMP |
| DEF-DED006 | Natural Deduction | SEM, CMP |
| DEF-DED007 | Sequent Calculus | SEM |
| DEF-DED008 | Tableau System | CMP |

### Imports

| ID | Concept | Provided by |
|----|---------|-------------|
| PRIM-BST001 | Set | BST |
| PRIM-BST009 | Function | BST |
| PRIM-BST010 | Finite Sequence | BST |
| PRIM-BST012 | Natural Number | BST |
| PRIM-BST013 | Mathematical Induction | BST |
| PRIM-SYN003 | Logical Connective | SYN |
| PRIM-SYN004 | Quantifier | SYN |
| PRIM-SYN012 | Formula | SYN |
| PRIM-SYN013 | Sentence | SYN |
| PRIM-SYN014 | Free Occurrence | SYN |
| PRIM-SYN017 | Subformula | SYN |
| PRIM-SYN018 | Equality Symbol | SYN |
| DEF-SYN001 | Substitution | SYN |
| DEF-SYN003 | Free Variables | SYN |

## 11. Completeness Argument

**Why these primitives cover the domain**: The 10 primitives + 10 definitions cover the full apparatus of syntactic deduction:
- **System components**: axiom schemas (001), non-logical axioms (002), rules (003), proof system (004), structural rules (007), sequents (008), assumption discharge (009).
- **Derivation apparatus**: derivation (005), provability (006), theorem (010).
- **Theory-level concepts**: syntactic consistency (DEF-001), maximal consistent sets (DEF-002), deductive closure (DEF-003), conservative extension (DEF-004).
- **Proof system architectures**: Hilbert (DEF-005), ND (DEF-006), SC (DEF-007), Tableaux (DEF-008).
- **Rule taxonomy**: derived rules (DEF-009), admissible rules (DEF-010).

**OL chapters**: `content/first-order-logic/proof-systems/`, `content/first-order-logic/natural-deduction/`, `content/first-order-logic/sequent-calculus/`, `content/first-order-logic/tableaux/`, `content/propositional-logic/proof-systems/`.

## 12. OpenLogic Mapping

| OL Chapter/Section | Maps to |
|---|---|
| `content/first-order-logic/proof-systems/` | PRIM-DED001--006, AX-DED001--003, DEF-DED005 |
| `content/first-order-logic/natural-deduction/` | DEF-DED006, PRIM-DED009 |
| `content/first-order-logic/sequent-calculus/` | DEF-DED007, PRIM-DED007, PRIM-DED008, THM-DED003 |
| `content/first-order-logic/tableaux/` | DEF-DED008 |
| `content/first-order-logic/completeness/` | DEF-DED001, DEF-DED002, THM-DED005 (used in CP-002) |
| `content/propositional-logic/proof-systems/` | PL fragments of PRIM-DED001--006, AX-DED001, AX-DED003(A1--A3) |

## 13. Self-Audit Checklist

- [x] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [x] Every THM depends only on previously listed AX/DEF/THM
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports
- [x] Dissolution argument is present and non-trivial
- [x] Extension points cover all three types: additive (modal), replacement (intuitionistic), structural (substructural)
- [x] Intra-domain dependency graph is acyclic
- [x] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [x] Motivating examples are present for all PRIM and key DEF entries
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Completeness argument addresses all relevant OL chapters
